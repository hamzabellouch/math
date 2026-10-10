import Mathlib
import OAI.NumberTheory.PrimePackets.IdealNorms
import OAI.NumberTheory.PrimePackets.ShannonEntropy

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace PrimeDegreePackets

 
def reverseNameEquiv {α : Type*} (N : ℕ) : (Fin N → α) ≃ (Fin N → α) where
  toFun f j := f j.rev
  invFun f j := f j.rev
  left_inv f := by funext j; simp
  right_inv f := by funext j; simp

lemma orbitName_inverse {Y α : Type*} [MeasurableSpace Y] (e : Y ≃ᵐ Y)
    (P : Y → α) (N : ℕ) :
    orbitName (e.symm : Y → Y) P N = fun y => reverseNameEquiv N
      (orbitName (e : Y → Y) P N ((e.symm : Y → Y)^[N-1] y)) := by
  funext y j
  change P ((e.symm : Y → Y)^[j.val] y) =
    P ((e : Y → Y)^[j.rev.val] ((e.symm : Y → Y)^[N-1] y))
  rw [Fin.val_rev,show N-(j.val+1)=N-1-j.val by omega]
  have hik : N-1-j.val+j.val = N-1 := by omega
  have hsplit : (e.symm : Y → Y)^[N-1] y =
      (e.symm : Y → Y)^[N-1-j.val] ((e.symm : Y → Y)^[j.val] y) := by
    rw [← Function.iterate_add_apply,hik]
  rw [hsplit]
  congr 1
  exact ((show Function.LeftInverse (e : Y → Y) (e.symm : Y → Y) from e.apply_symm_apply).iterate
    (N-1-j.val) ((e.symm : Y → Y)^[j.val] y)).symm

 

theorem orbitEntropy_inverse {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (e : Y ≃ᵐ Y) (he : MeasurePreserving e μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    observationEntropy μ (orbitName (e.symm : Y → Y) P N) =
      observationEntropy μ (orbitName (e : Y → Y) P N) := by
  rw [orbitName_inverse,observationEntropy_equiv]
  exact observationEntropy_comp_preserving μ _
    (orbitName_measurable_fiber e.measurable hP N) ((MeasurePreserving.symm e he).iterate (N-1))

 

theorem measureEntropy_inverse {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (e : Y ≃ᵐ Y) (he : MeasurePreserving e μ μ) :
    measureEntropy μ (e.symm : Y → Y) = measureEntropy μ (e : Y → Y) := by
  unfold measureEntropy
  apply iSup_congr
  intro k
  apply iSup_congr
  intro P
  apply iSup_congr
  intro hP
  simp_rw [observationEntropyRate,orbitEntropy_inverse μ e he P hP]

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def RelationDiameter {Y : Type*} (R : Y → Y → Prop) (E : Set Y) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, R x y

 

def StepCover {Y : Type*} (T : Y → Y) (R : Y → Y → Prop) (M : ℕ) : Prop :=
  ∀ E : Set Y, RelationDiameter R E → ∃ F : Fin M → Set Y,
    E ⊆ ⋃ i, F i ∧ ∀ i, F i ⊆ E ∧ RelationDiameter R (T '' F i)

lemma stepCover_of_image {Y : Type*} {T : Y → Y} {R : Y → Y → Prop} {M : ℕ}
    (h : StepCover T R M) (j : ℕ) (E : Set Y)
    (hE : RelationDiameter R (T^[j] '' E)) :
    ∃ F : Fin M → Set Y, E ⊆ ⋃ i, F i ∧ ∀ i, F i ⊆ E ∧
      RelationDiameter R (T^[j+1] '' F i) := by
  obtain ⟨F,hcov,hF⟩ := h _ hE
  refine ⟨fun i => E ∩ T^[j] ⁻¹' F i, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcov ⟨x,hx,rfl⟩)
    exact Set.mem_iUnion.mpr ⟨i,hx,hi⟩
  · intro i
    refine ⟨Set.inter_subset_left,?_⟩
    rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact (hF i).2 _ ⟨_,hu.2,rfl⟩ _ ⟨_,hv.2,rfl⟩

 

theorem orbit_name_cover {Y α : Type*} {T : Y → Y} {R : Y → Y → Prop}
    {M : ℕ} (hM : 1 ≤ M) (hstep : StepCover T R M)
    (P : Y → α) (bad : α → Prop) [DecidablePred bad]
    (hfine : ∀ a, ¬bad a → RelationDiameter R {y | P y = a})
    (N : ℕ) (a : ℕ → α) (ha : ¬bad (a 0))
    (E : Set Y) (hE : ∀ y ∈ E, ∀ j ≤ N, P (T^[j] y) = a j) :
    ∃ s : Finset (Set Y), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^(((Finset.range (N+1)).filter fun j => bad (a j)).card) ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ N, RelationDiameter R (T^[j] '' F) := by
  classical
  have hM0 : 0 < M := hM
  have aux : ∀ k ≤ N, ∃ s : Finset (Set Y), E ⊆ ⋃ F ∈ s, F ∧
      s.card ≤ M^((Finset.range (k+1)).filter fun j => bad (a j)).card ∧
      ∀ F ∈ s, F ⊆ E ∧ ∀ j ≤ k, RelationDiameter R (T^[j] '' F) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨{E},by simp,?_,?_⟩
      · simp only [Finset.card_singleton]
        exact Nat.one_le_pow _ _ hM0
      · intro F hF
        have hFE : F = E := by simpa using hF
        subst F
        refine ⟨Set.Subset.refl _,?_⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        simp only [Function.iterate_zero,Set.image_id]
        intro x hx y hy
        apply hfine (a 0) ha
        · exact hE x hx 0 (by omega)
        · exact hE y hy 0 (by omega)
    | succ k ih =>
      obtain ⟨s,hcov,hcard,hs⟩ := ih (by omega)
      by_cases hb : bad (a (k+1))
      · choose F hFc hFp using fun C : s => stepCover_of_image hstep k C.val
          ((hs C.val C.property).2 k le_rfl)
        let t : Finset (Set Y) := s.attach.biUnion fun C => Finset.univ.image (F C)
        refine ⟨t,?_,?_,?_⟩
        · intro x hx
          obtain ⟨C,hC,hxC⟩ := Set.mem_iUnion₂.mp (hcov hx)
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hFc ⟨C,hC⟩ hxC)
          exact Set.mem_iUnion₂.mpr ⟨F ⟨C,hC⟩ i,
            Finset.mem_biUnion.mpr ⟨⟨C,hC⟩,by simp,Finset.mem_image.mpr ⟨i,by simp,rfl⟩⟩,hi⟩
        · have ht : t.card ≤ s.card*M := by
            calc
              t.card ≤ ∑ C ∈ s.attach, (Finset.univ.image (F C)).card := Finset.card_biUnion_le
              _ ≤ ∑ _C ∈ s.attach, M := Finset.sum_le_sum fun C _ =>
                (Finset.card_image_le).trans_eq (by simp)
              _ = s.card*M := by simp
          calc
            t.card ≤ s.card*M := ht
            _ ≤ M^((Finset.range (k+1)).filter fun j => bad (a j)).card *M :=
              Nat.mul_le_mul_right M hcard
            _ = _ := by
              rw [Finset.range_add_one (n := k+1),Finset.filter_insert]
              simp only [hb,ite_true]
              rw [Finset.card_insert_of_notMem, pow_succ]
              simp only [Finset.mem_filter,Finset.mem_range,lt_self_iff_false,false_and,not_false_eq_true]
        · intro C hC
          obtain ⟨D,hD,hCi⟩ := Finset.mem_biUnion.mp hC
          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hCi
          refine ⟨(hFp D i).1.trans (hs D.val D.property).1,?_⟩
          intro j hj
          by_cases heq : j = k+1
          · subst j
            exact (hFp D i).2
          · have hd := (hs D.val D.property).2 j (by omega)
            intro x hx y hy
            exact hd x (Set.image_mono (hFp D i).1 hx) y (Set.image_mono (hFp D i).1 hy)
      · refine ⟨s,hcov,?_,?_⟩
        · simpa only [Finset.range_add_one (n := k+1),Finset.filter_insert,hb,ite_false] using hcard
        · intro C hC
          refine ⟨(hs C hC).1,?_⟩
          intro j hj
          by_cases heq : j = k+1
          · subst j
            rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩
            apply hfine (a (k+1)) hb
            · exact hE u ((hs C hC).1 hu) (k+1) (by omega)
            · exact hE v ((hs C hC).1 hv) (k+1) (by omega)
          · exact (hs C hC).2 j (by omega)
  exact aux N le_rfl

 

theorem orbit_name_mass {Y α : Type*} [MeasurableSpace Y]
    {T : Y → Y} {R : Y → Y → Prop} {M : ℕ} (hM : 1 ≤ M)
    (hstep : StepCover T R M) (μ : Measure Y)
    (P : Y → α) (bad : α → Prop) [DecidablePred bad]
    (hfine : ∀ a, ¬bad a → RelationDiameter R {y | P y = a})
    (N : ℕ) (a : ℕ → α) (ha : ¬bad (a 0))
    (E : Set Y) (hE : ∀ y ∈ E, ∀ j ≤ N, P (T^[j] y) = a j)
    (B : ℝ≥0∞)
    (hB : ∀ x ∈ E, μ {y | ∀ j ≤ N, R (T^[j] x) (T^[j] y)} ≤ B) :
    μ E ≤ (M^((Finset.range (N+1)).filter fun j => bad (a j)).card : ℕ)*B := by
  classical
  obtain ⟨s,hcov,hcard,hs⟩ := orbit_name_cover hM hstep P bad hfine N a ha E hE
  have hF : ∀ F ∈ s, μ F ≤ B := by
    intro F hF
    by_cases hne : F.Nonempty
    · obtain ⟨x,hx⟩ := hne
      apply (measure_mono (show F ⊆ {y | ∀ j ≤ N, R (T^[j] x) (T^[j] y)} from ?_)).trans
        (hB x ((hs F hF).1 hx))
      intro y hy j hj
      exact (hs F hF).2 j hj _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    · simp only [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  calc
    μ E ≤ μ (⋃ F ∈ s, F) := measure_mono hcov
    _ ≤ ∑ F ∈ s, μ F := measure_biUnion_finset_le _ _
    _ ≤ ∑ _F ∈ s, B := Finset.sum_le_sum hF
    _ = s.card*B := by simp [nsmul_eq_mul]
    _ ≤ (M^((Finset.range (N+1)).filter fun j => bad (a j)).card : ℕ)*B :=
by
      gcongr

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical
namespace PrimeDegreePackets

def visitCount {Y : Type*} (T : Y → Y) (B : Set Y) (N : ℕ) (x : Y) : ℕ :=
  ((Finset.range N).filter fun j => T^[j] x ∈ B).card

lemma visitCount_cast {Y : Type*} (T : Y → Y) (B : Set Y) (N : ℕ) (x : Y) :
    (visitCount T B N x : ℝ) = ∑ j ∈ Finset.range N, B.indicator (fun _ => (1:ℝ)) (T^[j] x) := by
  classical
  rw [visitCount,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hx : T^[j] x ∈ B <;> simp [hx]

lemma integrable_visitCount {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {B : Set Y} (hB : MeasurableSet B) (N : ℕ) :
    Integrable (fun x => (visitCount T B N x : ℝ)) μ := by
  simp only [visitCount_cast]
  apply integrable_finsetSum
  intro j _
  exact (hT.iterate j).integrable_comp_of_integrable ((integrable_const (1:ℝ)).indicator hB)

lemma integral_visitCount {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {B : Set Y} (hB : MeasurableSet B) (N : ℕ) :
    (∫ x, (visitCount T B N x : ℝ) ∂μ) = N*μ.real B := by
  simp only [visitCount_cast]
  rw [integral_finsetSum]
  · have hj (j : ℕ) : (∫ x, B.indicator (fun _ => (1:ℝ)) (T^[j] x) ∂μ) = μ.real B := by
      have H := integral_map (hT.iterate j).measurable.aemeasurable
        ((measurable_const.indicator hB).aestronglyMeasurable (μ := Measure.map T^[j] μ) :
          AEStronglyMeasurable (B.indicator (fun _ => (1:ℝ))) (Measure.map T^[j] μ))
      rw [(hT.iterate j).map_eq] at H
      rw [← H]
      simp [integral_indicator hB,measureReal_def]
    simp only [hj,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  · intro j _
    exact (hT.iterate j).integrable_comp_of_integrable ((integrable_const (1:ℝ)).indicator hB)

lemma measurable_visitCount {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {B : Set Y} (hB : MeasurableSet B) (N : ℕ) :
    Measurable (fun x => (visitCount T B N x : ℝ)) := by
  simp only [visitCount_cast]
  exact Finset.measurable_sum _ fun j _ => (measurable_const.indicator hB).comp (hT.iterate j)

 

theorem measure_many_visits {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {B : Set Y} (hB : MeasurableSet B) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε*N < (visitCount T B N x : ℝ)} ≤ ENNReal.ofReal (μ.real B/ε) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hi := (integrable_visitCount μ hT hB N).div_const (ε*N)
  have hnon : 0 ≤ᵐ[μ] fun x => (visitCount T B N x : ℝ)/(ε*N) :=
    ae_of_all _ fun x => div_nonneg (Nat.cast_nonneg _) (mul_pos hε hn).le
  have H := hi.measure_le_integral hnon (s := {x | ε*N < (visitCount T B N x : ℝ)})
    (fun x hx => (le_div_iff₀ (mul_pos hε hn)).mpr (by simpa only [one_mul] using hx.le))
  rw [integral_div,integral_visitCount μ hT hB N] at H
  convert H using 2
  field_simp

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
namespace PrimeDegreePackets

lemma matrixBall_mono {n : ℕ} {r s : ℝ} (hrs : r ≤ s) :
    matrixBall n r ⊆ matrixBall n s := by
  intro g hg i j
  exact (hg i j).trans_le hrs

 

lemma inverse_entries_uniform (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ g ∈ matrixBall n 1, ∀ i j, |g⁻¹.1 i j| ≤ C := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ) := {m | ∀ i j, |m i j| ≤ 2}
  have hK : IsCompact K := by
    simpa only [K,Set.matrix,Set.mem_Icc,abs_le] using
      (show IsCompact (Set.Icc (-2:ℝ) 2) from isCompact_Icc).matrix
  have hpre : IsCompact (Subtype.val ⁻¹' K : Set (G n)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hK
  have hc : Continuous (fun g : G n => g⁻¹.1) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous.comp continuous_inv
  obtain ⟨C,hC⟩ := hpre.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0+1,by positivity,?_⟩
  intro g hg i j
  have hgin : g.1 ∈ K := by
    intro i j
    have H := hg i j
    have H1 : |(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ 1 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply,hij]
    calc
      |g.1 i j| = |(g.1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j)+
          (1 : Matrix (Fin n) (Fin n) ℝ) i j| := by congr 1; ring
      _ ≤ |g.1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| +
          |(1 : Matrix (Fin n) (Fin n) ℝ) i j| := abs_add_le _ _
      _ ≤ 2 := by linarith
  calc
    |g⁻¹.1 i j| = ‖g⁻¹.1 i j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖g⁻¹.1 i‖ := norm_le_pi_norm _ _
    _ ≤ ‖g⁻¹.1‖ := norm_le_pi_norm _ _
    _ ≤ C := hC g hgin
    _ ≤ max C 0+1 := by linarith [le_max_left C 0]

 
lemma left_div_entry_bound {n : ℕ} (g h : G n) {C b : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ i j, |g⁻¹.1 i j| ≤ C)
    (hgh : ∀ i j, |h.1 i j-g.1 i j| ≤ b) :
    ∀ i j, |(g⁻¹*h).1 i j-(1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ n*C*b := by
  intro i j
  have heq : (g⁻¹*h).1 - (1 : Matrix (Fin n) (Fin n) ℝ) = g⁻¹.1*(h.1-g.1) := by
    rw [Matrix.mul_sub]
    simp only [← Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,Matrix.SpecialLinearGroup.coe_one]
  change |((g⁻¹*h).1-(1 : Matrix (Fin n) (Fin n) ℝ)) i j| ≤ _
  rw [heq,Matrix.mul_apply]
  calc
    |∑ k, g⁻¹.1 i k*(h.1-g.1) k j| ≤ ∑ k, |g⁻¹.1 i k*(h.1-g.1) k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, C*b := Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact mul_le_mul (hg i k) (hgh k j) (abs_nonneg _) hC
    _ = n*C*b := by simp; ring

 

theorem small_matrix_ball_cover (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℝ, 0 < r → L*r ≤ 1 →
      ∃ F : Fin M → Set (G n), matrixBall n (L*r) ⊆ ⋃ i, F i ∧
        ∀ i, F i ⊆ matrixBall n (L*r) ∧
          RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (F i) := by
  classical
  obtain ⟨C,hC,HC⟩ := inverse_entries_uniform n
  let ε : ℝ := 1/(4*((n:ℝ)+1)*(C+1))
  have hden : 0 < 4*((n:ℝ)+1)*(C+1) := by positivity
  have hε : 0 < ε := by exact one_div_pos.mpr hden
  have hε1 : ε ≤ 1 := by
    apply (div_le_one hden).mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hbudget : (n:ℝ)*C*ε ≤ 1/4 := by
    change (n:ℝ)*C*(1/(4*((n:ℝ)+1)*(C+1))) ≤ 1/4
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  let e : (Fin n × Fin n) ≃ Fin (Fintype.card (Fin n × Fin n)) := Fintype.equivFin _
  obtain ⟨s,_,_,hs⟩ := cube_grid_cover (Fintype.card (Fin n × Fin n)) hL hε hε1
  have hsne : s.Nonempty := by
    obtain ⟨u,hu,_⟩ := hs 0 (by simpa using fun _ => hL)
    exact ⟨u,hu⟩
  let : Nonempty s := hsne.to_subtype
  let f : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s,Fintype.card_pos,?_⟩
  intro r hr hLr
  let q (g : G n) (t : Fin (Fintype.card (Fin n × Fin n))) : ℝ :=
    (g.1 (e.symm t).1 (e.symm t).2 - (1 : Matrix (Fin n) (Fin n) ℝ) (e.symm t).1 (e.symm t).2)/r
  let F (i : Fin (Fintype.card s)) : Set (G n) :=
    {g | g ∈ matrixBall n (L*r) ∧ ∀ t, |q g t-(f i).val t| < ε}
  refine ⟨F,?_,?_⟩
  · intro g hg
    have hq : ∀ t, |q g t| ≤ L := by
      intro t
      dsimp [q]
      rw [abs_div,abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr (hg _ _).le
    obtain ⟨u,hu,hgu⟩ := hs (q g) hq
    exact Set.mem_iUnion.mpr ⟨f.symm ⟨u,hu⟩,hg,by simpa using hgu⟩
  · intro i
    refine ⟨fun _ hg => hg.1,?_⟩
    intro g hg h hh
    have hg1 := matrixBall_mono hLr hg.1
    have hdiff : ∀ j k, |h.1 j k-g.1 j k| ≤ 2*ε*r := by
      intro j k
      have H : |q h (e (j,k))-q g (e (j,k))| ≤ 2*ε := by
        calc
          _ = |(q h (e (j,k))-(f i).val (e (j,k))) +
              ((f i).val (e (j,k))-q g (e (j,k)))| := by congr 1; ring
          _ ≤ |q h (e (j,k))-(f i).val (e (j,k))| +
              |(f i).val (e (j,k))-q g (e (j,k))| := abs_add_le _ _
          _ ≤ 2*ε := by rw [abs_sub_comm ((f i).val _)]; linarith [hg.2 (e (j,k)),hh.2 (e (j,k))]
      have he : h.1 j k-g.1 j k = (q h (e (j,k))-q g (e (j,k)))*r := by
        simp only [q,Equiv.symm_apply_apply]
        field_simp
        ring
      rw [he,abs_mul,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_right H hr.le
    have Hbound := left_div_entry_bound g h hC.le (HC g hg1) hdiff
    intro j k
    apply (Hbound j k).trans_lt
    nlinarith [mul_le_mul_of_nonneg_right hbudget hr.le]

end PrimeDegreePackets

open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
namespace PrimeDegreePackets

lemma one_mem_matrixBall (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 : G n) ∈ matrixBall n r := by
  intro i j
  simpa using hr

lemma matrixBall_nhds_basis {n : ℕ} {U : Set (G n)} (hU : U ∈ 𝓝 (1 : G n)) :
    ∃ r : ℝ, 0 < r ∧ matrixBall n r ⊆ U := by
  have hv : Topology.IsInducing (fun g : G n => g.1) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.isInducing
  rw [hv.nhds_eq_comap] at hU
  obtain ⟨V,hV,hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r,hr,fun g hg => hVU (hsub ?_)⟩
  change dist g.1 (1 : G n).1 < r
  rw [dist_eq_norm]
  exact (Matrix.norm_lt_iff hr).mpr hg

 

lemma local_uniform_chart_injective {n : ℕ} (x : X n) :
    ∃ U : Set (X n), IsOpen U ∧ x ∈ U ∧ ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ U, Set.InjOn (fun g => rightAction y g) (matrixBall n r) := by
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨V,hVo,hgV,hVi⟩ :=
      (quotient_covering n).isLocalHomeomorph.isLocallyInjective g
    have hpre : (fun u : G n => g*u) ⁻¹' V ∈ 𝓝 (1 : G n) := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      simpa using hVo.mem_nhds hgV
    obtain ⟨W,hWo,h1W,hWW⟩ := exists_open_nhds_one_mul_subset hpre
    obtain ⟨r,hr,hrW⟩ := matrixBall_nhds_basis (hWo.mem_nhds h1W)
    refine ⟨(fun u => Quotient.mk _ (g*u)) '' W, ?_, ?_, r,hr,?_⟩
    · rw [← Set.image_image]
      exact (quotient_covering n).isOpenMap _ ((Homeomorph.mulLeft g).isOpenMap _ hWo)
    · exact ⟨1,h1W,by simp⟩
    · rintro y ⟨u,hu,rfl⟩ v hv w hw heq
      have hgv : g*(u*v) ∈ V := hWW (Set.mul_mem_mul hu (hrW hv))
      have hgw : g*(u*w) ∈ V := hWW (Set.mul_mem_mul hu (hrW hw))
      have He : g*(u*v) = g*(u*w) := hVi hgv hgw (by
        change Quotient.mk _ ((g*u)*v) = Quotient.mk _ ((g*u)*w) at heq
        simpa only [mul_assoc] using heq)
      exact mul_left_cancel (mul_left_cancel He)

 
theorem compact_uniform_chart_injective {n : ℕ} (K : Set (X n)) (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K,
      Set.InjOn (fun g => rightAction x g) (matrixBall n r) := by
  choose U hUo hxU r hr hU using local_uniform_chart_injective (n := n)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hUo (by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hxU x⟩)
  let t : Finset ℝ := insert 1 (s.image r)
  have ht : t.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨t.min' ht,?_,?_⟩
  · have hm := Finset.min'_mem t ht
    rcases Finset.mem_insert.mp hm with hm | hm
    · rw [hm]; norm_num
    · obtain ⟨x,_,hxr⟩ := Finset.mem_image.mp hm
      rw [← hxr]
      exact hr x
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    apply (hU y x hxy).mono
    apply matrixBall_mono
    exact Finset.min'_le t (r y) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨y,hy,rfl⟩))

end PrimeDegreePackets
end
end

end OAI
