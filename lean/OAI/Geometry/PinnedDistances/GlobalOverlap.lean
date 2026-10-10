import OAI.Geometry.PinnedDistances.FiberOverlap

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Grid
open MeasureTheory

lemma truncated_error_integrable {z w : ℂ} (hne : z ≠ w) (t : ℝ) :
    Integrable (fun ω => max (|error ω z w|-t) 0) fullLaw :=
  (((error_integrable_full hne).abs.sub (integrable_const t)).sup (integrable_zero _ _ _))

lemma truncated_error_mean {z w : ℂ} (hne : z ≠ w) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, max (|error ω z w|-t) 0 ∂fullLaw) ≤ 4*Real.exp (-t) := by
  have hm : Measurable (fun ω => max (|error ω z w|-t) 0) :=
    ((measurable_error hne).abs.sub_const t).max measurable_const
  have hn (ω : FullSample) : 0 ≤ max (|error ω z w|-t) 0 := le_max_right _ _
  have hi := truncated_error_integrable hne t
  have he : IntegrableOn (fun u : ℝ => (4*Real.exp (-t))*Real.exp (-u)) (Set.Ioi 0) volume := by
    simpa only [neg_one_mul, IntegrableOn] using
      (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul (4*Real.exp (-t))
  have hb : (∫⁻ ω, ENNReal.ofReal (max (|error ω z w|-t) 0) ∂fullLaw) ≤
      ENNReal.ofReal (4*Real.exp (-t)) := by
    rw [lintegral_eq_lintegral_meas_lt fullLaw
      (Filter.Eventually.of_forall hn) hm.aemeasurable]
    calc
      _ ≤ ∫⁻ u : ℝ in Set.Ioi 0, ENNReal.ofReal ((4*Real.exp (-t))*Real.exp (-u)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := hu
        have hs : {ω : FullSample | u < max (|error ω z w|-t) 0} =
            {ω : FullSample | u+t < |error ω z w|} := by
          ext ω
          simp only [Set.mem_ofPred_eq,lt_max_iff]
          constructor
          · rintro (h | h) <;> linarith
          · intro h; exact Or.inl (by linarith)
        rw [hs, ← ENNReal.ofReal_toReal (measure_ne_top fullLaw _)]
        have hh := abs_error_tail_full hne (add_nonneg hu.le ht)
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ 4*Real.exp (-(u+t)) := hh
          _ = _ := by rw [neg_add,Real.exp_add]; ring
      _ = ENNReal.ofReal (4*Real.exp (-t)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
        congr 1
        rw [integral_const_mul]
        have hz := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)
        simp only [neg_one_mul,mul_zero,Real.exp_zero,neg_div_neg_eq,div_one] at hz
        rw [hz,mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

lemma truncated_sum_bound (a b H : ℝ) :
    max (|a+b|-H) 0 ≤ 2*max (|a|-H/2) 0 + 2*max (|b|-H/2) 0 := by
  apply max_le
  · have ht := abs_add_le a b
    have h₁ := le_max_left (|a|-H/2) 0
    have h₂ := le_max_left (|b|-H/2) 0
    have h₃ := le_max_right (|a|-H/2) 0
    have h₄ := le_max_right (|b|-H/2) 0
    linarith
  · positivity

lemma paired_error_mean {z₁ w₁ z₂ w₂ : ℂ} (h₁ : z₁ ≠ w₁) (h₂ : z₂ ≠ w₂)
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ ω, max (|error ω z₁ w₁ + error ω z₂ w₂|-H) 0 ∂fullLaw) ≤
      16*Real.exp (-H/2) := by
  have hi : Integrable (fun ω => max (|error ω z₁ w₁ + error ω z₂ w₂|-H) 0) fullLaw := by
    exact Integrable.sup (((error_integrable_full h₁).add (error_integrable_full h₂)).abs.sub
      (integrable_const H)) (integrable_zero _ _ _)
  have hia := truncated_error_integrable h₁ (H/2)
  have hib := truncated_error_integrable h₂ (H/2)
  have hh := integral_mono hi ((hia.const_mul 2).add (hib.const_mul 2))
    (fun ω => truncated_sum_bound (error ω z₁ w₁) (error ω z₂ w₂) H)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hia.const_mul 2) (hib.const_mul 2)] at hh
  simp only [integral_const_mul] at hh
  have hta := truncated_error_mean h₁ (div_nonneg hH (by norm_num : (0:ℝ)≤2))
  have htb := truncated_error_mean h₂ (div_nonneg hH (by norm_num : (0:ℝ)≤2))
  rw [neg_div'] at hta htb
  linarith

end WeakPinned.Grid

namespace WeakPinned.Global
open Hierarchy Variance SmallFiber
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma arch_fiber_defect (v : InfinitePlace K) (a b : P) (hab : a ≠ b) (t : K)
    (ht : (Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) :
    (fun ω => (arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)) =ᵐ[Grid.fullLaw]
      (fun ω => Grid.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Grid.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))) := by
  have he := Arithmetic.raw_fiber_identity v.val (Z₁ a-Z₁ b) (Z₂ a-Z₂ b)
    (sub_ne_zero.mpr (h₁.ne hab)) (sub_ne_zero.mpr (h₂.ne hab))
  rw [ht] at he
  change -Real.log (v (Z₁ a-Z₁ b)) + -Real.log (v (Z₂ a-Z₂ b)) = -Real.log (v t) at he
  filter_upwards [arch_value_ae Z₁ h₁ v hab,arch_value_ae Z₂ h₂ v hab] with ω hA hB
  rw [hA,hB]
  simp only [Grid.error,← map_sub,InfinitePlace.norm_embedding_eq]
  linarith

lemma arch_defect_mean (v : InfinitePlace K) (a b : P) (hab : a ≠ b) (t : K)
    (ht : (Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) (H : ℝ) (hH : 0 ≤ H) :
    (∫ ω, max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0 ∂Grid.fullLaw) ≤
      16*Real.exp (-H/2) := by
  have he := arch_fiber_defect Z₁ Z₂ h₁ h₂ v a b hab t ht
  have he' : (fun ω => max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0) =ᵐ[Grid.fullLaw]
      (fun ω => max (|Grid.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Grid.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))|-H) 0) := by
    filter_upwards [he] with ω hh
    rw [hh]
  rw [integral_congr_ae he']
  exact Grid.paired_error_mean (embedding_ne Z₁ h₁ v hab) (embedding_ne Z₂ h₂ v hab) hH

lemma arch_weighted_defect (v : InfinitePlace K) (w : I → ℝ) (p : I → P → ℝ)
    (x : I → P) (t : I → K) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1)
    (hp : ∀ i y, 0 ≤ p i y) (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (H : ℝ) (hH : 0 ≤ H) :
    (∫ ω, ∑ i, w i*∑ y, p i y*max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0 ∂Grid.fullLaw) ≤ 16*Real.exp (-H/2) := by
  have hi (i : I) (y : P) : Integrable (fun ω => max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0) Grid.fullLaw :=
    ((((arch_integrable Z₁ h₁ v _ _).add (arch_integrable Z₂ h₂ v _ _)).add (integrable_const _)).abs.sub
      (integrable_const H)).sup (integrable_zero _ _ _)
  rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum (s:=Finset.univ)
    (fun y _ => (hi i y).const_mul _)).const_mul _)]
  simp_rw [integral_const_mul,integral_finsetSum _ (fun y _ => (hi _ y).const_mul _),integral_const_mul]
  calc
    _ ≤ ∑ i, w i * ∑ y, p i y*(16*Real.exp (-H/2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : p i y=0
      · simp [hy]
      · have hxy : x i ≠ y := by intro he; rw [← he,hx i] at hy; exact hy rfl
        exact mul_le_mul_of_nonneg_left (arch_defect_mean Z₁ Z₂ h₁ h₂ v _ _ hxy _ (ht i y hy) H hH) (hp i y)
    _ = _ := by simp only [← Finset.sum_mul,hp1,one_mul,hW]

lemma arch_small_fiber (hn : 2 ≤ Fintype.card P) (v : InfinitePlace K)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, (∫ ω, (arch Z₁ v ω).mass C ∂Grid.fullLaw)*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, (∫ ω, (arch Z₁ v ω).mass C ∂Grid.fullLaw)*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, ∫ ω, (arch Z₁ v ω).potential y ∂Grid.fullLaw)+
        (∑ y, ∫ ω, (arch Z₂ v ω).potential y ∂Grid.fullLaw)) +
      2*lam*B*(∑ C, (∫ ω, (arch Z₂ v ω).mass C ∂Grid.fullLaw)*pairCell Finset.univ C) + 2*lam*H +
      16*Real.exp (-H/2) := by
  have hiM₁ (C : Finset P) := Depth.integrable_mass_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn C
  have hiM₂ (C : Finset P) := Depth.integrable_mass_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn C
  have hiS₁ (y : P) := Depth.integrable_potential_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn y
  have hiS₂ (y : P) := Depth.integrable_potential_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn y
  have hiE (i : I) (y : P) : Integrable (fun ω => max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0) Grid.fullLaw := by
    have hd := ((arch_integrable Z₁ h₁ v (x i) y).add (arch_integrable Z₂ h₂ v (x i) y)).add
      (integrable_const (Real.log (v (t i))))
    exact (hd.abs.sub (integrable_const H)).sup (integrable_zero _ _ _)
  have hA := (integrable_finsetSum (s:=Finset.univ) (fun C _ => (hiM₁ C).mul_const (pairCell Finset.univ C))).const_mul (2*lam/τ^2)
  have hS := ((integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₁ y)).add
    (integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₂ y))).const_mul (B*τ/Fintype.card P)
  have hA' := (integrable_finsetSum (s:=Finset.univ) (fun C _ => (hiM₂ C).mul_const (pairCell Finset.univ C))).const_mul (2*lam*B)
  have hE := integrable_finsetSum (s:=Finset.univ) (fun i _ =>
    (integrable_finsetSum (s:=Finset.univ) (fun y _ => (hiE i y).const_mul (p i y))).const_mul (w i))
  have hb := integral_mono (integrable_finsetSum (s:=Finset.univ) (fun C _ => (hiM₁ C).mul_const (slice w p x lam C)))
    ((((hA.add hS).add hA').add (integrable_const (2*lam*H))).add hE)
    (fun ω => by
      simpa only [Pi.add_apply,sub_neg_eq_add] using
        (local_small_fiber_reduced (arch Z₁ v ω) (arch Z₂ v ω) w p x hw hW hp hp1 hx hn
          (fun i => -Real.log (v (t i))) B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom))
  have hI₁ := integral_add (((hA.add hS).add hA').add (integrable_const (2*lam*H))) hE
  have hI₂ := integral_add ((hA.add hS).add hA') (integrable_const (2*lam*H))
  have hI₃ := integral_add (hA.add hS) hA'
  have hI₄ := integral_add hA hS
  have hI₅ := integral_add (integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₁ y))
    (integrable_finsetSum (s:=Finset.univ) (fun y _ => hiS₂ y))
  simp only [Pi.add_apply] at hb hI₁ hI₂ hI₃ hI₄ hI₅
  rw [hI₁,hI₂,hI₃,hI₄] at hb
  simp only [integral_const,probReal_univ,one_smul,integral_const_mul] at hb
  rw [hI₅] at hb
  rw [integral_finsetSum _ (fun C _ => (hiM₁ C).mul_const (slice w p x lam C)),
    integral_finsetSum _ (fun C _ => (hiM₁ C).mul_const (pairCell Finset.univ C)),
    integral_finsetSum _ (fun C _ => (hiM₂ C).mul_const (pairCell Finset.univ C)),
    integral_finsetSum _ (fun y _ => hiS₁ y),integral_finsetSum _ (fun y _ => hiS₂ y)] at hb
  simp only [integral_mul_const] at hb
  have he := arch_weighted_defect Z₁ Z₂ h₁ h₂ v w p x t hw hW hp hp1 hx ht H hH
  linarith

lemma finite_small_fiber (hn : 2 ≤ Fintype.card P) (v : FinitePlace K)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ))
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    (∑ C, (finite Z₁ h₁ v).mass C*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, (finite Z₁ h₁ v).mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, (finite Z₁ h₁ v).potential y)+(∑ y, (finite Z₂ h₂ v).potential y)) +
      2*lam*B*(∑ C, (finite Z₂ h₂ v).mass C*pairCell Finset.univ C) := by
  have hb := local_small_fiber_reduced (finite Z₁ h₁ v) (finite Z₂ h₂ v) w p x hw hW hp hp1 hx hn
    (fun i => -Real.log (v (t i))) B τ lam 0 hB hlam hlam2 hτ hτ1 hτn (le_refl _) hdom
  have he (i : I) (y : P) : p i y * max (|(finite Z₁ h₁ v).value (x i) y+
      (finite Z₂ h₂ v).value (x i) y- -Real.log (v (t i))|-0) 0=0 := by
    by_cases hy : p i y=0
    · simp [hy]
    · have hxy : x i ≠ y := by intro he; rw [← he,hx i] at hy; exact hy rfl
      have hh := Arithmetic.raw_fiber_identity v.val (Z₁ (x i)-Z₁ y) (Z₂ (x i)-Z₂ y)
        (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
      change -Real.log (v (Z₁ (x i)-Z₁ y)) + -Real.log (v (Z₂ (x i)-Z₂ y)) =
        -Real.log (v ((Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y))) at hh
      rw [ht i y hy] at hh
      simp only [finite,hxy,reduceIte,hh,sub_self,abs_zero,max_self,mul_zero]
  simpa only [he,Finset.sum_const_zero,mul_zero,add_zero] using hb

omit h₁ h₂ in
lemma finite_zero_outside {Z : P → K} (hZ : Function.Injective Z) (v : FinitePlace K)
    (hv : v ∉ badPlaces Z hZ) : ∀ a b, (finite Z hZ v).value a b=0 := by
  intro a b
  by_cases hab : a=b
  · simp [finite,hab]
  · have hunit : v (Z a-Z b)=1 := by
      by_contra h
      exact hv ((badPlaces_mem Z hZ v).mpr ⟨a,b,hab,h⟩)
    simp [finite,hab,hunit]

omit h₁ h₂ in
lemma finite_mass_zero {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (v : FinitePlace K) (hv : v ∉ badPlaces Z hZ) (C : Finset P) : (finite Z hZ v).mass C=0 := by
  have hz := (finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)
  by_cases hC : C.card ≤ 1
  · exact (finite Z hZ v).mass_singleton C hC
  · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1<C.card)
    have hl := (finite Z hZ v).mass_le_overlap hn C a b hab ha hb
    rw [hz.2.2 a b hab] at hl
    exact le_antisymm hl ((finite Z hZ v).mass_nonneg C)

omit h₁ h₂ in
lemma sum_finite_mass {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (C : Finset P) :
    (∑ v ∈ V, (finite Z hZ v).mass C) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).mass C := by
  symm
  exact Finset.sum_subset hV (fun v _ hv => finite_mass_zero hZ hn v hv C)

omit h₁ h₂ in
lemma sum_finite_potential {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (a : P) :
    (∑ v ∈ V, (finite Z hZ v).potential a) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential a := by
  symm
  exact Finset.sum_subset hV (fun v _ hv =>
    ((finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)).2.1 a)

omit h₁ h₂ in
def placeAverage (V : Finset (FinitePlace K)) (A : InfinitePlace K → ℝ) (F : FinitePlace K → ℝ) : ℝ :=
  (∑ v, Arithmetic.archWeight v * A v) + (Module.finrank ℚ K:ℝ)⁻¹ * ∑ v ∈ V, F v

omit h₁ h₂ in
lemma placeAverage_mono (V : Finset (FinitePlace K)) {A A' : InfinitePlace K → ℝ} {F F' : FinitePlace K → ℝ}
    (hA : ∀ v, A v ≤ A' v) (hF : ∀ v ∈ V, F v ≤ F' v) : placeAverage V A F ≤ placeAverage V A' F' := by
  apply add_le_add
  · exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hA v) (Arithmetic.archWeight_nonneg v))
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (by positivity)

omit h₁ h₂ in
lemma placeAverage_add (V : Finset (FinitePlace K)) (A A' : InfinitePlace K → ℝ) (F F' : FinitePlace K → ℝ) :
    placeAverage V (fun v => A v+A' v) (fun v => F v+F' v) = placeAverage V A F + placeAverage V A' F' := by
  simp only [placeAverage,mul_add,Finset.sum_add_distrib]
  ring

omit h₁ h₂ in
lemma placeAverage_mul (V : Finset (FinitePlace K)) (a : ℝ) (A : InfinitePlace K → ℝ) (F : FinitePlace K → ℝ) :
    placeAverage V (fun v => a*A v) (fun v => a*F v) = a*placeAverage V A F := by
  simp only [placeAverage,Finset.mul_sum,mul_add]
  congr 1
  · exact Finset.sum_congr rfl (fun v _ => by ring)
  · exact Finset.sum_congr rfl (fun v _ => by ring)

omit h₁ h₂ in
lemma placeAverage_arch_const (V : Finset (FinitePlace K)) (a : ℝ) :
    placeAverage V (fun _ => a) (fun _ => 0) = a := by
  simp only [placeAverage,Finset.sum_const_zero,mul_zero,add_zero,← Finset.sum_mul,Arithmetic.sum_archWeight,one_mul]

omit h₁ h₂ in
lemma cellIntegral_placeAverage {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (f : Finset P → ℝ) :
    weightedIntegral (cellMass Z hZ) f = placeAverage V
      (fun v => ∑ C, (∫ ω, (arch Z v ω).mass C ∂Grid.fullLaw)*f C)
      (fun v => ∑ C, (finite Z hZ v).mass C*f C) := by
  simp only [weightedIntegral,cellMass,placeAverage,add_mul,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.sum_congr rfl (fun C _ => by ring)
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [← Finset.sum_mul, sum_finite_mass hZ hn V hV,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun C _ => by rw [← Finset.mul_sum]; ring)

omit h₁ h₂ in
lemma potentialIntegral_placeAverage {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) :
    (∑ y, S Z hZ y) = placeAverage V
      (fun v => ∑ y, ∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw)
      (fun v => ∑ y, (finite Z hZ v).potential y) := by
  simp only [S,placeAverage,Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm (s:=V)]
    simp_rw [sum_finite_potential hZ hn V hV,Finset.mul_sum]

lemma arithmetic_small_fiber_one (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    weightedIntegral (cellMass Z₁ h₁) (slice w p x lam) ≤
      (2*lam/τ^2)*weightedIntegral (cellMass Z₁ h₁) (pairCell Finset.univ) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, S Z₁ h₁ y)+(∑ y, S Z₂ h₂ y)) +
      2*lam*B*weightedIntegral (cellMass Z₂ h₂) (pairCell Finset.univ) + 2*lam*H +
      16*Real.exp (-H/2) := by
  classical
  let V := badPlaces Z₁ h₁ ∪ badPlaces Z₂ h₂
  have hV₁ : badPlaces Z₁ h₁ ⊆ V := Finset.subset_union_left
  have hV₂ : badPlaces Z₂ h₂ ⊆ V := Finset.subset_union_right
  have hf (v : FinitePlace K) : (∑ C, (finite Z₁ h₁ v).mass C*slice w p x lam C) ≤
      (2*lam/τ^2)*(∑ C, (finite Z₁ h₁ v).mass C*pairCell Finset.univ C) +
      B*τ/(Fintype.card P:ℝ)*((∑ y, (finite Z₁ h₁ v).potential y)+(∑ y, (finite Z₂ h₂ v).potential y)) +
      2*lam*B*(∑ C, (finite Z₂ h₂ v).mass C*pairCell Finset.univ C) + 0 + 0 := by
    simpa only [add_zero] using finite_small_fiber Z₁ Z₂ h₁ h₂ hn v w p x t hw hW hp hp1 hx ht B τ lam hB hlam hlam2 hτ hτ1 hτn hdom
  have hb := placeAverage_mono V
    (fun v => arch_small_fiber Z₁ Z₂ h₁ h₂ hn v w p x t hw hW hp hp1 hx ht B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom)
    (fun v _ => hf v)
  simp only [placeAverage_add,placeAverage_mul,placeAverage_arch_const] at hb
  rw [← cellIntegral_placeAverage h₁ hn V hV₁,← cellIntegral_placeAverage h₁ hn V hV₁,
    ← cellIntegral_placeAverage h₂ hn V hV₂,← potentialIntegral_placeAverage h₁ hn V hV₁,
    ← potentialIntegral_placeAverage h₂ hn V hV₂] at hb
  exact hb

/-- The global small-fiber estimate, uniformly over number fields, places and configurations. -/

lemma arithmetic_small_fiber (hn : 2 ≤ Fintype.card P)
    (w : I → ℝ) (p : I → P → ℝ) (x : I → P) (t : I → K)
    (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1) (hp : ∀ i y, 0 ≤ p i y)
    (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (B τ lam H : ℝ) (hB : 0 ≤ B) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 1/2)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτn : 2 ≤ τ*(Fintype.card P:ℝ)) (hH : 0 ≤ H)
    (hdom : ∀ a b, a ≠ b → edgeLaw w p x a b ≤ B/((Fintype.card P:ℝ)*((Fintype.card P:ℝ)-1))) :
    weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (slice w p x lam) ≤
      (2*lam/τ^2+2*lam*B)*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (pairCell Finset.univ) +
      2*B*τ/(Fintype.card P:ℝ)*(∑ y, totalPotential Z₁ Z₂ h₁ h₂ y) + 4*lam*H +
      32*Real.exp (-H/2) := by
  have hA := arithmetic_small_fiber_one Z₁ Z₂ h₁ h₂ hn w p x t hw hW hp hp1 hx ht B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  have ht' : ∀ i y, p i y ≠ 0 → (Z₂ (x i)-Z₂ y)*(Z₁ (x i)-Z₁ y)=t i := by
    intro i y hy
    rw [mul_comm]
    exact ht i y hy
  have hB' := arithmetic_small_fiber_one Z₂ Z₁ h₂ h₁ hn w p x t hw hW hp hp1 hx ht' B τ lam H hB hlam hlam2 hτ hτ1 hτn hH hdom
  simp only [weightedIntegral,totalMass,totalPotential,add_mul,Finset.sum_add_distrib] at hA hB' ⊢
  linear_combination hA+hB'

end WeakPinned.Global

noncomputable section
open Filter
open scoped Topology

end
end
end
end
end
end
end

end OAI
