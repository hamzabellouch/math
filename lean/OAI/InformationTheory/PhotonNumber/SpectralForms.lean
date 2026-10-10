import OAI.InformationTheory.PhotonNumber.BeamForms
import OAI.InformationTheory.PhotonNumber.Generator
import OAI.InformationTheory.PhotonNumber.Interpolation

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory

namespace BKM

section
open scoped ComplexConjugate
variable {J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def reindexBasis (b : HilbertBasis J ℂ E) (e : K ≃ J) : HilbertBasis K ℂ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (b ∘ e) = Set.range b := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨e.symm j, by simp⟩
    rw [hr]
    exact b.dense_span.ge)
@[simp] theorem reindexBasis_apply (b : HilbertBasis J ℂ E) (e : K ≃ J) (i : K) :
    reindexBasis b e i = b (e i) := by simp [reindexBasis]

omit [CompleteSpace E] in
 theorem basis_hasSum_normSq (b : HilbertBasis J ℂ E) (x : E) :
    HasSum (fun j => Complex.normSq (inner ℂ (b j) x)) (‖x‖^2) := by
  simpa only [Complex.normSq_eq_norm_sq] using TraceEnsemble.basis_hasSum_norm_sq b x

def entry (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) : ℂ := inner ℂ (b i) (Z (b j))

 theorem entry_adjoint (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    entry b Z.adjoint i j = conj (entry b Z j i) := by
  rw [entry, ContinuousLinearMap.adjoint_inner_right, entry, inner_conj_symm]

omit [CompleteSpace E] in
 theorem hasSum_column (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (j : J) :
    HasSum (fun i => Complex.normSq (entry b Z i j)) (‖Z (b j)‖^2) := basis_hasSum_normSq b _

 theorem hasSum_row (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i : J) :
    HasSum (fun j => Complex.normSq (entry b Z i j)) (‖Z.adjoint (b i)‖^2) := by
  have h := hasSum_column b Z.adjoint i
  simpa only [entry_adjoint, Complex.normSq_conj] using h

omit [CompleteSpace E] in
 theorem weighted_column_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (Z : E →L[ℂ] E) :
    Summable (fun ij : J × J => p ij.2*Complex.normSq (entry b Z ij.1 ij.2)) := by
  have hb (j : J) : ‖Z (b j)‖^2 ≤ ‖Z‖^2 := by
    have h := Z.le_opNorm (b j)
    rw [b.orthonormal.norm_eq_one j, mul_one] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have ht : Summable (fun j => p j*‖Z (b j)‖^2) :=
    (hs.mul_right (‖Z‖^2)).of_nonneg_of_le (fun j => mul_nonneg (hp j) (sq_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (hb j) (hp j))
  have hh : Summable (fun ji : J × J => p ji.1*Complex.normSq (entry b Z ji.2 ji.1)) := by
    rw [summable_prod_of_nonneg (fun ji => mul_nonneg (hp _) (Complex.normSq_nonneg _))]
    exact ⟨fun j => ((hasSum_column b Z j).mul_left (p j)).summable,
      by simpa only [tsum_mul_left, (hasSum_column b Z _).tsum_eq] using ht⟩
  exact (Equiv.prodComm J J).summable_iff.mpr hh

 theorem weighted_row_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (Z : E →L[ℂ] E) :
    Summable (fun ij : J × J => p ij.1*Complex.normSq (entry b Z ij.1 ij.2)) := by
  have hh := (Equiv.prodComm J J).summable_iff.mpr (weighted_column_summable b p hp hs Z.adjoint)
  simpa only [Function.comp_def, Equiv.prodComm_apply, Prod.swap, entry_adjoint, Complex.normSq_conj] using hh

 theorem logMean_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (Z : E →L[ℂ] E) :
    Summable (fun ij : J × J => DiagonalForms.System.logMean (p ij.1) (p ij.2)*
      Complex.normSq (entry b Z ij.1 ij.2)) := by
  have hh := ((weighted_row_summable b p (fun j => (hp j).le) hs Z).add
    (weighted_column_summable b p (fun j => (hp j).le) hs Z)).div_const 2
  apply hh.of_nonneg_of_le
  · intro ij
    exact mul_nonneg (DiagonalForms.System.logMean_pos (hp _) (hp _)).le (Complex.normSq_nonneg _)
  · intro ij
    convert! mul_le_mul_of_nonneg_right (DiagonalForms.System.logMean_le_arithmetic (hp ij.1) (hp ij.2))
        (Complex.normSq_nonneg (entry b Z ij.1 ij.2)) using 1
    ring

end

open scoped BigOperators
variable {J : Type*}

 theorem tendsto_square_finset : Tendsto (fun s : Finset J => s ×ˢ s) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro t
  filter_upwards [eventually_ge_atTop (t.image Prod.fst ∪ t.image Prod.snd)] with s hs
  intro ij hij
  exact Finset.mem_product.mpr ⟨hs (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ij,hij,rfl⟩)),
    hs (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ij,hij,rfl⟩))⟩

 theorem hasSum_square_finset {v : J × J → ℝ} {a : ℝ} (h : HasSum v a) :
    Tendsto (fun s : Finset J => ∑ i ∈ s, ∑ j ∈ s, v (i,j)) atTop (𝓝 a) := by
  classical
  simpa only [Function.comp_def, Finset.sum_product] using h.comp tendsto_square_finset

 theorem finite_hessian_to_variance (v : J × J → ℝ) (m : J → ℝ) (μ A α γ W : ℝ)
    (hv : HasSum v A) (hm : HasSum m μ) (hα : 0 < α)
    (h : ∀ (s : Finset J) (t : ℝ),
      2*γ*t*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-μ*(∑ i ∈ s, m i)) ≤
        α*t^2*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-(∑ i ∈ s, m i)^2)+W) :
    γ^2*(A-μ^2) ≤ α*W := by
  have hQ := hasSum_square_finset hv
  have hlo : Tendsto (fun s : Finset J =>
      2*γ*(γ/α)*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-μ*(∑ i ∈ s, m i))) atTop
        (𝓝 (2*γ*(γ/α)*(A-μ*μ))) := (hQ.sub (hm.const_mul μ)).const_mul _
  have hup : Tendsto (fun s : Finset J =>
      α*(γ/α)^2*((∑ i ∈ s, ∑ j ∈ s, v (i,j))-(∑ i ∈ s, m i)^2)+W) atTop
        (𝓝 (α*(γ/α)^2*(A-μ^2)+W)) := ((hQ.sub (hm.pow 2)).const_mul _).add_const _
  have hh := le_of_tendsto_of_tendsto hlo hup (Filter.Eventually.of_forall fun s => h s (γ/α))
  have hh' := mul_le_mul_of_nonneg_left hh hα.le
  have hne := hα.ne'
  field_simp at hh'
  nlinarith

end BKM

namespace SpectralTests
open scoped BigOperators ComplexConjugate
variable {A I P : Type*}

def space (g : A → I → ℂ) : Submodule ℂ (I → ℂ) := Submodule.span ℂ (Set.range g)

theorem frequency_finite (g : A → I → ℂ) (v : I → P) (q : A → P)
    (hg : ∀ a i, g a i ≠ 0 → v i = q a) (z : I → ℂ) (hz : z ∈ space g) :
    ∃ s : Finset P, ∀ i, z i ≠ 0 → v i ∈ s := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨{q a}, fun i hi => by simpa only [Finset.mem_singleton] using hg a i hi⟩
  | zero => exact ⟨∅, fun i hi => (hi rfl).elim⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    refine ⟨s ∪ t, fun i hi => ?_⟩
    by_cases hxi : x i = 0
    · have hyi : y i ≠ 0 := by simpa only [Pi.add_apply, hxi, zero_add] using hi
      exact Finset.mem_union.mpr (Or.inr (ht i hyi))
    · exact Finset.mem_union.mpr (Or.inl (hs i hxi))
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, fun i hi => hs i ?_⟩
    intro hxi
    apply hi
    simp [hxi]

def multiplier (v : I → P) (w : P → ℂ) : (I → ℂ) →ₗ[ℂ] (I → ℂ) where
  toFun z i := w (v i)*z i
  map_add' x y := by ext i; simp only [Pi.add_apply, mul_add]
  map_smul' c x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem multiplier_generator (g : A → I → ℂ) (v : I → P) (q : A → P)
    (hg : ∀ a i, g a i ≠ 0 → v i = q a) (w : P → ℂ) (a : A) :
    multiplier v w (g a) = w (q a) • g a := by
  ext i
  change w (v i)*g a i=w (q a)*g a i
  by_cases hi : g a i = 0
  · simp [hi]
  · rw [hg a i hi]

theorem multiplier_mem (g : A → I → ℂ) (v : I → P) (q : A → P)
    (hg : ∀ a i, g a i ≠ 0 → v i = q a) (z : I → ℂ) (hz : z ∈ space g) (w : P → ℂ) :
    multiplier v w z ∈ space g := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [multiplier_generator g v q hg]
    exact (space g).smul_mem _ (Submodule.subset_span ⟨a,rfl⟩)
  | zero => simpa only [map_zero] using (space g).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (space g).add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using (space g).smul_mem c hx

theorem square_summable_iff (z : I → ℂ) :
    Summable (fun i => Complex.normSq (z i)) ↔ Memℓp z 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)]
  simp only [Complex.normSq_eq_norm_sq, ENNReal.toReal_ofNat, Real.rpow_two]

theorem mass_summable (g : A → I → ℂ) (hg : ∀ a, Summable (fun i => Complex.normSq (g a i)))
    (z : I → ℂ) (hz : z ∈ space g) : Summable (fun i => Complex.normSq (z i)) := by
  rw [square_summable_iff]
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a,rfl⟩ := hx; exact (square_summable_iff _).mp (hg a)
  | zero => exact (show Memℓp (0 : I → ℂ) 2 from zero_memℓp)
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_smul c

end SpectralTests

namespace CenteredTests
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def entryMap (b : HilbertBasis J ℂ E) (w : J × J → ℝ) :
    (E →L[ℂ] E) →ₗ[ℂ] (J × J → ℂ) where
  toFun Z ij := (Real.sqrt (w ij) : ℂ)*BKM.entry b Z ij.1 ij.2
  map_add' X Y := by ext ij; simp [BKM.entry, mul_add]
  map_smul' c X := by ext ij; simp [BKM.entry, mul_left_comm]

@[simp] theorem entryMap_apply (b : HilbertBasis J ℂ E) (w : J × J → ℝ)
    (Z : E →L[ℂ] E) (ij : J × J) :
    entryMap b w Z ij = (Real.sqrt (w ij) : ℂ)*BKM.entry b Z ij.1 ij.2 := rfl

theorem entryMap_injective (b : HilbertBasis J ℂ E) (w : J × J → ℝ) (hw : ∀ ij, 0 < w ij) :
    Function.Injective (entryMap b w) := by
  intro X Y h
  have hb (j : J) : X (b j)=Y (b j) := by
    apply b.repr.injective
    ext i
    simp only [b.repr_apply_apply]
    have hh := congrFun h (i,j)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (hw (i,j)))) hh
  ext x
  have hX := (b.hasSum_repr x).mapL X
  have hY := (b.hasSum_repr x).mapL Y
  apply hX.unique
  convert! hY using 1
  ext j
  simp only [map_smul, hb]

def generator (b : HilbertBasis J ℂ E) (p : J → ℝ) (ij : J × J) : E →L[ℂ] E := by
  classical
  exact InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2) -
    (if ij.1=ij.2 then (p ij.1:ℂ) else 0) • ContinuousLinearMap.id ℂ E

theorem generator_entry [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ) (ij kl : J × J) :
    BKM.entry b (generator b p ij) kl.1 kl.2 =
      (if kl.1=ij.1 ∧ kl.2=ij.2 then (1:ℂ) else 0)-
      (if ij.1=ij.2 then (p ij.1:ℂ) else 0)*(if kl.1=kl.2 then 1 else 0) := by
  classical
  simp only [generator, BKM.entry, sub_apply,
    smul_apply, ContinuousLinearMap.id_apply, InnerProductSpace.rankOne_apply,
    inner_sub_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  split_ifs <;> simp_all

theorem generator_frequency (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    {P : Type*} (v : J × J → P) (q : P) (hv : ∀ j, v (j,j)=q)
    (ij kl : J × J) (hz : entryMap b w (generator b p ij) kl ≠ 0) : v kl=v ij := by
  classical
  have hg : BKM.entry b (generator b p ij) kl.1 kl.2 ≠ 0 := by
    intro hh; apply hz; simp [hh]
  rw [generator_entry] at hg
  by_cases hij : ij.1=ij.2
  · have hkl : kl.1=kl.2 := by
      by_contra hk
      have hp : ¬ (kl.1=ij.1 ∧ kl.2=ij.2) := fun hf => hk (hf.1.trans (hij.trans hf.2.symm))
      simp [hp,hk] at hg
    calc v kl=v (kl.2,kl.2) := by congr 1; exact Prod.ext hkl rfl
         _=q := hv _
         _=v (ij.2,ij.2) := (hv _).symm
         _=v ij := by congr 1; exact Prod.ext hij.symm rfl
  · have hkl : kl.1=ij.1 ∧ kl.2=ij.2 := by
      by_contra hk
      simp [hij,hk] at hg
    exact congrArg v (Prod.ext hkl.1 hkl.2)

def operatorSpace (b : HilbertBasis J ℂ E) (p : J → ℝ) : Submodule ℂ (E →L[ℂ] E) :=
  Submodule.span ℂ (Set.range (generator b p))

def coordinates (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) :
    Submodule ℂ (J × J → ℂ) := (operatorSpace b p).map (entryMap b w)

theorem coordinates_eq_span (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) :
    coordinates b p w = SpectralTests.space (fun ij => entryMap b w (generator b p ij)) := by
  rw [coordinates, operatorSpace, Submodule.map_span, ← Set.range_comp]
  rfl

variable [CompleteSpace E]

theorem coordinates_mass (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : Summable p) (h : ℝ) (hh : 0 ≤ h) (z : coordinates b p (fun ij => h*DiagonalForms.System.logMean (p ij.1) (p ij.2))) :
    Summable (fun ij => Complex.normSq (z.val ij)) := by
  obtain ⟨Z, _hZ, he⟩ := z.property
  rw [← he]
  have hsum := (BKM.logMean_summable b p hp hs Z).mul_left h
  convert! hsum using 1
  ext ij
  simp only [entryMap_apply, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (mul_nonneg hh (DiagonalForms.System.logMean_pos (hp _) (hp _)).le)]
  ring

end CenteredTests

namespace ThermalMetric

section
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem observable_summable (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) (Z : E →L[ℂ] E) :
    Summable (fun a : J × J => metricCoefficient t (p a.1) (p a.2) *
      ‖BKM.entry b Z a.1 a.2‖^2) := by
  have hc := BKM.weighted_column_summable b p (fun j => (hp j).le) hs Z
  have hr := BKM.weighted_row_summable b p (fun j => (hp j).le) hs Z
  simp only [Complex.normSq_eq_norm_sq] at hc hr
  apply Summable.of_nonneg_of_le
    (fun a => mul_nonneg (metricCoefficient_pos ht (hp _) (hp _)).le (sq_nonneg _)) _
    (((hr.mul_left t).add (hc.mul_left (t+1))).mul_left (h t/2))
  intro a
  have hh := DiagonalForms.System.logMean_le_arithmetic (mul_pos ht (hp a.1))
    (mul_pos (by positivity : 0<t+1) (hp a.2))
  have hm : metricCoefficient t (p a.1) (p a.2) =
      h t*DiagonalForms.System.logMean (t*p a.1) ((t+1)*p a.2) := by
    rw [metricCoefficient, mul_assoc, tilted_logMean ht (hp _) (hp _)]
  rw [hm]
  have hh' := mul_le_mul_of_nonneg_left hh (h_pos ht).le
  nlinarith [mul_le_mul_of_nonneg_right hh' (sq_nonneg ‖BKM.entry b Z a.1 a.2‖)]

def observableMap (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) :
    (E →L[ℂ] E) →ₗ[ℂ] lp (fun _ : J × J => ℂ) 2 where
  toFun Z := weightedVector (fun a => metricCoefficient t (p a.1) (p a.2))
    (fun a => BKM.entry b Z a.1 a.2) (observable_summable b p hp hs t ht Z)
    (fun a => (metricCoefficient_pos ht (hp _) (hp _)).le)
  map_add' Z U := by ext a; simp [BKM.entry, mul_add]
  map_smul' c Z := by ext a; simp [BKM.entry, mul_left_comm]

@[simp] theorem observableMap_apply (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t)
    (Z : E →L[ℂ] E) (a : J × J) :
    observableMap b p hp hs t ht Z a =
      (Real.sqrt (metricCoefficient t (p a.1) (p a.2)) : ℂ) * BKM.entry b Z a.1 a.2 := rfl

@[simp] theorem observableMap_id (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) :
    observableMap b p hp hs t ht (ContinuousLinearMap.id ℂ E) = identityVector t ht p hp hs := by
  classical
  ext a
  simp [BKM.entry, identityVector, identityEntry,
    orthonormal_iff_ite.mp b.orthonormal]

end

section
open scoped ComplexConjugate
variable {J : Type*}

def centerProjection (e : lp (fun _ : J => ℂ) 2) :
    lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2 :=
  ContinuousLinearMap.id ℂ _ - (innerSL ℂ e).smulRight e

@[simp] theorem centerProjection_apply (e x : lp (fun _ : J => ℂ) 2) :
    centerProjection e x=x-inner ℂ e x • e := rfl

theorem centerProjection_mem (e x : lp (fun _ : J => ℂ) 2)
    (he : inner ℂ e e=1) : centerProjection e x ∈ (innerSL ℂ e).ker := by
  change inner ℂ e (x-inner ℂ e x • e)=0
  simp only [inner_sub_right, inner_smul_right, he, mul_one, sub_self]

theorem centerProjection_eq (e x : lp (fun _ : J => ℂ) 2)
    (hx : x ∈ (innerSL ℂ e).ker) : centerProjection e x=x := by
  change inner ℂ e x=0 at hx
  simp only [centerProjection_apply, hx, zero_smul, sub_zero]

variable [DecidableEq J]

theorem centered_single_dense (e : lp (fun _ : J => ℂ) 2)
    (he : inner ℂ e e=1) :
    (Submodule.span ℂ (Set.range (fun j => centerProjection e (lp.single 2 j (1:ℂ))))).topologicalClosure =
      (innerSL ℂ e).ker := by
  classical
  let S := Submodule.span ℂ (Set.range (fun j => centerProjection e (lp.single 2 j (1:ℂ))))
  apply le_antisymm
  · apply S.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact centerProjection_mem _ _ he
    · exact (innerSL ℂ e).isClosed_ker
  · intro x hx
    have hh := (lp.hasSum_single (by norm_num : (2:ENNReal)≠⊤) x).mapL (centerProjection e)
    rw [centerProjection_eq _ _ hx] at hh
    apply S.isClosed_topologicalClosure.mem_of_tendsto hh
    apply Filter.Eventually.of_forall
    intro s
    apply S.topologicalClosure.sum_mem
    intro j _
    have hs : centerProjection e (lp.single 2 j (x j)) ∈ S := by
      have hsingle : lp.single (E := fun _ : J => ℂ) 2 j (x j)=(x j) • lp.single 2 j (1:ℂ) := by
        rw [← lp.single_smul]
        simp only [smul_eq_mul, mul_one]
      rw [hsingle, map_smul]
      exact S.smul_mem _ (Submodule.subset_span ⟨j,rfl⟩)
    exact S.le_topologicalClosure hs

@[simp] theorem identityVector_apply (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (ij : J × J) :
    identityVector r hr p hp hs ij =
      if ij.1=ij.2 then (Real.sqrt (p ij.1):ℂ) else 0 := by
  classical
  simp only [identityVector, weightedVector_apply, identityEntry]
  split_ifs with he
  · rw [he, metricCoefficient_self hr (hp _)]; simp
  · simp

theorem identityVector_inner (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) :
    inner ℂ (identityVector r hr p hp hs.summable) (identityVector r hr p hp hs.summable)=1 := by
  classical
  have hh := hasSum_diagonal (Complex.hasSum_ofReal.mpr hs)
  have ht := lp.hasSum_inner (𝕜 := ℂ) (identityVector r hr p hp hs.summable)
    (identityVector r hr p hp hs.summable)
  apply ht.unique
  convert! hh using 1
  ext ij
  simp only [identityVector_apply, RCLike.inner_apply]
  split_ifs with he
  · simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp _).le]
  · simp

def matrixGenerator (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (ij : J × J) : lp (fun _ : J × J => ℂ) 2 := by
  classical
  exact (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ) • lp.single 2 ij 1 -
    (if ij.1=ij.2 then (p ij.1:ℂ) else 0) • identityVector r hr p hp hs

theorem matrixGenerator_projection (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (ij : J × J) :
    matrixGenerator r hr p hp hs ij =
      (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ) •
        centerProjection (identityVector r hr p hp hs) (lp.single 2 ij 1) := by
  classical
  rw [matrixGenerator, centerProjection_apply, smul_sub, smul_smul]
  congr 1
  congr 1
  rw [lp.inner_single_right, RCLike.inner_apply, one_mul, identityVector_apply]
  split_ifs with he
  · rw [he, metricCoefficient_self hr (hp _), Complex.conj_ofReal,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (hp _).le]
  · simp

theorem matrixGenerator_dense (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) :
    (Submodule.span ℂ (Set.range (matrixGenerator r hr p hp hs.summable))).topologicalClosure =
      centeredSpace r hr p hp hs.summable := by
  let e := identityVector r hr p hp hs.summable
  have hh := centered_single_dense e (identityVector_inner r hr p hp hs)
  have he : Submodule.span ℂ (Set.range (matrixGenerator r hr p hp hs.summable))=
      Submodule.span ℂ (Set.range (fun j => centerProjection e (lp.single 2 j (1:ℂ)))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨ij,rfl⟩
      rw [matrixGenerator_projection]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij,rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨ij,rfl⟩
      have hz : (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (metricCoefficient_pos hr (hp _) (hp _)))
      have ht : centerProjection e (lp.single 2 ij 1)=
          (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ)⁻¹ • matrixGenerator r hr p hp hs.summable ij := by
        rw [matrixGenerator_projection, smul_smul, inv_mul_cancel₀ hz, one_smul]
      dsimp only
      rw [ht]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij,rfl⟩)
  rw [he]
  exact hh
end

open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[simp] theorem observableMap_generator [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (t : ℝ) (ht : 0 < t) (ij : J × J) :
    observableMap b p hp hs t ht (CenteredTests.generator b p ij) =
      matrixGenerator t ht p hp hs ij := by
  classical
  ext kl
  simp only [observableMap_apply, CenteredTests.generator_entry, matrixGenerator,
    lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    lp.single_apply, Pi.single_apply, identityVector_apply]
  by_cases he : kl=ij
  · subst kl
    by_cases hd : ij.1=ij.2
    · simp only [hd, metricCoefficient_self ht (hp _), ite_true, and_self,
        mul_one]
      ring
    · simp [hd]
  · have he' : ¬ (kl.1=ij.1 ∧ kl.2=ij.2) := fun hh => he (Prod.ext hh.1 hh.2)
    simp only [ite_eq_right he, ite_eq_right he', mul_zero, zero_sub]
    by_cases hd : kl.1=kl.2
    · simp only [hd, metricCoefficient_self ht (hp _), ite_true]
      ring
    · simp [hd]

theorem observable_core_dense (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (t : ℝ) (ht : 0 < t) :
    ((CenteredTests.operatorSpace b p).map
      (observableMap b p hp hs.summable t ht)).topologicalClosure =
      centeredSpace t ht p hp hs.summable := by
  classical
  rw [CenteredTests.operatorSpace, Submodule.map_span, ← Set.range_comp]
  simpa only [Function.comp_def, observableMap_generator] using
    matrixGenerator_dense t ht p hp hs

theorem functional_bound_of_core (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (t : ℝ) (ht : 0 < t)
    (q : lp (fun _ : J × J => ℂ) 2 →L[ℂ] ℂ) (C : ℝ)
    (hc : ∀ Z, Z ∈ CenteredTests.operatorSpace b p →
      ‖q (observableMap b p hp hs.summable t ht Z)‖ ≤
        C*‖observableMap b p hp hs.summable t ht Z‖) :
    ∀ x ∈ centeredSpace t ht p hp hs.summable, ‖q x‖ ≤ C*‖x‖ := by
  have hclosed : IsClosed {x : lp (fun _ : J × J => ℂ) 2 | ‖q x‖ ≤ C*‖x‖} :=
    isClosed_le q.continuous.norm (continuous_const.mul continuous_norm)
  have himage : (((CenteredTests.operatorSpace b p).map
      (observableMap b p hp hs.summable t ht) : Submodule ℂ _) : Set _) ⊆
        {x | ‖q x‖ ≤ C*‖x‖} := by
    rintro _ ⟨Z,hZ,rfl⟩
    exact hc Z hZ
  have hh := closure_minimal himage hclosed
  rw [← Submodule.topologicalClosure_coe, observable_core_dense b p hp hs t ht] at hh
  exact hh

theorem restricted_norm_bound_of_core (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (t : ℝ) (ht : 0 < t)
    (q : lp (fun _ : J × J => ℂ) 2 →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ Z, Z ∈ CenteredTests.operatorSpace b p →
      ‖q (observableMap b p hp hs.summable t ht Z)‖ ≤
        C*‖observableMap b p hp hs.summable t ht Z‖) :
    ‖q.comp (centeredSpace t ht p hp hs.summable).subtypeL‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  exact functional_bound_of_core b p hp hs t ht q C hc x.val x.property

end ThermalMetric

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace CenteredTests
open scoped BigOperators
variable {J T E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def includeRange (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) :
    coordinates b p w →ₗ[ℂ] LinearMap.range (entryMap b w) where
  toFun z := ⟨z.val, by obtain ⟨Z, _hZ, he⟩ := z.property; exact ⟨Z,he⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def realize (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ) (hw : ∀ ij, 0 < w ij) :
    coordinates b p w →ₗ[ℂ] (E →L[ℂ] E) :=
  (LinearEquiv.ofInjective (entryMap b w) (entryMap_injective b w hw)).symm.toLinearMap.comp
    (includeRange b p w)

omit [CompleteSpace E] in
theorem realize_entries (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    (hw : ∀ ij, 0 < w ij) (z : coordinates b p w) : entryMap b w (realize b p w hw z)=z.val := by
  exact LinearEquiv.ofInjective_symm_apply (h := entryMap_injective b w hw) _ _

omit [CompleteSpace E] in
theorem realize_mem (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    (hw : ∀ ij, 0 < w ij) (z : coordinates b p w) : realize b p w hw z ∈ operatorSpace b p := by
  obtain ⟨Z,hZ,he⟩ := z.property
  have hh : realize b p w hw z=Z := entryMap_injective b w hw ((realize_entries b p w hw z).trans he.symm)
  rw [hh]
  exact hZ

def system (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : Summable p)
    (h : ℝ) (hh : 0 < h) (v : J × J → P) (q : P) (hv : ∀ j, v (j,j)=q)
    (targetParam : T → P) (L : (E →L[ℂ] E) →ₗ[ℂ] (T → ℂ)) : DiagonalForms.System P (J × J) T where
  sourceParam := v
  targetParam := targetParam
  tests := coordinates b p (fun ij => h*DiagonalForms.System.logMean (p ij.1) (p ij.2))
  map := L.comp (realize b p _ (fun ij => mul_pos hh (DiagonalForms.System.logMean_pos (hp _) (hp _))))
  mass_summable z := coordinates_mass b p hp hs h hh.le z
  finite_values z := by
    apply SpectralTests.frequency_finite (fun ij => entryMap b _ (generator b p ij)) v v
      (generator_frequency b p _ v q hv) z.val
    rw [← coordinates_eq_span]
    exact z.property
  multiplier_mem z w := by
    apply (SetLike.ext_iff.mp (coordinates_eq_span b p _) _).mpr
    exact SpectralTests.multiplier_mem (fun ij => entryMap b _ (generator b p ij)) v v
      (generator_frequency b p _ v q hv) z.val (by rw [← coordinates_eq_span]; exact z.property) w

end CenteredTests

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

theorem reference_plus {r : ℝ} (hr : 0<r) :
    (1/h r)*f (-h r/2)*Real.exp (-h r/2)=r := by
  have hh := logMean_arithmetic_plus hr (show 0<r+1 by linarith)
  rw [logMean_reference hr] at hh
  have he : -h r/2=(Real.log r-Real.log (r+1))/2 := by unfold h; ring
  simpa only [he] using hh

theorem reference_minus {r : ℝ} (hr : 0<r) :
    (1/h r)*f (-h r/2)*Real.exp (-(-h r/2))=r+1 := by
  have hh := logMean_arithmetic_minus hr (show 0<r+1 by linarith)
  rw [logMean_reference hr] at hh
  have he : -h r/2=(Real.log r-Real.log (r+1))/2 := by unfold h; ring
  simpa only [he] using hh
end ThermalMetric

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

structure Space (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  I : Type
  basis : HilbertBasis I ℂ E
  p : I → ℝ
  pos : ∀ i, 0 < p i
  sum : HasSum p 1
  r : ℝ
  rpos : 0 < r

namespace Space
variable (S : Space E)
def param (ij : S.I × S.I) : ℝ × ℝ := (S.r, frequency S.r (S.p ij.1) (S.p ij.2))
def base (ij : S.I × S.I) : ℝ := h S.r*logMean (S.p ij.1) (S.p ij.2)
theorem base_pos (ij : S.I × S.I) : 0 < S.base ij := mul_pos (h_pos S.rpos) (logMean_pos (S.pos _) (S.pos _))
def coords : (E →L[ℂ] E) →ₗ[ℂ] (S.I × S.I → ℂ) := CenteredTests.entryMap S.basis S.base

theorem coords_norm (Z : E →L[ℂ] E) (ij : S.I × S.I) :
    Complex.normSq (S.coords Z ij)=S.base ij*Complex.normSq (BKM.entry S.basis Z ij.1 ij.2) := by
  simp only [coords, CenteredTests.entryMap_apply, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (S.base_pos ij).le]

def quad (w : ℝ × ℝ → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  ∑' ij, w (S.param ij)*Complex.normSq (S.coords Z ij)

def plus (q : ℝ × ℝ) : ℝ := (1/h q.1)*f (h q.1*q.2/2)*Real.exp (h q.1*q.2/2)
def minus (q : ℝ × ℝ) : ℝ := (1/h q.1)*f (h q.1*q.2/2)*Real.exp (-(h q.1*q.2/2))

theorem freq_cancel (ij : S.I × S.I) :
    h S.r*(S.param ij).2/2=(Real.log (S.p ij.1)-Real.log (S.p ij.2))/2 := by
  dsimp [param, frequency]
  field_simp [(h_pos S.rpos).ne']

theorem plus_entry (Z : E →L[ℂ] E) (ij : S.I × S.I) :
    plus (S.param ij)*Complex.normSq (S.coords Z ij)=S.p ij.1*Complex.normSq (BKM.entry S.basis Z ij.1 ij.2) := by
  rw [coords_norm]
  simp only [plus, param]
  have hh := logMean_arithmetic_plus (S.pos ij.1) (S.pos ij.2)
  have hf := S.freq_cancel ij
  change h S.r*frequency S.r (S.p ij.1) (S.p ij.2)/2 = _ at hf
  rw [hf]
  dsimp [base]
  have hn := (h_pos S.rpos).ne'
  field_simp
  linear_combination Complex.normSq (BKM.entry S.basis Z ij.1 ij.2)*hh

theorem minus_entry (Z : E →L[ℂ] E) (ij : S.I × S.I) :
    minus (S.param ij)*Complex.normSq (S.coords Z ij)=S.p ij.2*Complex.normSq (BKM.entry S.basis Z ij.1 ij.2) := by
  rw [coords_norm]
  simp only [minus, param]
  have hh := logMean_arithmetic_minus (S.pos ij.1) (S.pos ij.2)
  have hf := S.freq_cancel ij
  change h S.r*frequency S.r (S.p ij.1) (S.p ij.2)/2 = _ at hf
  rw [hf]
  dsimp [base]
  have hn := (h_pos S.rpos).ne'
  field_simp
  linear_combination Complex.normSq (BKM.entry S.basis Z ij.1 ij.2)*hh

theorem plus_summable (Z : E →L[ℂ] E) : Summable (fun ij => plus (S.param ij)*Complex.normSq (S.coords Z ij)) := by
  simpa only [S.plus_entry Z] using BKM.weighted_row_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z

theorem minus_summable (Z : E →L[ℂ] E) : Summable (fun ij => minus (S.param ij)*Complex.normSq (S.coords Z ij)) := by
  simpa only [S.minus_entry Z] using BKM.weighted_column_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z

theorem constant_summable (c : ℝ) (Z : E →L[ℂ] E) :
    Summable (fun ij => c*Complex.normSq (S.coords Z ij)) := by
  have hh := ((BKM.logMean_summable S.basis S.p S.pos S.sum.summable Z).mul_left (h S.r)).mul_left c
  simpa only [S.coords_norm, base, mul_assoc] using hh
end Space

abbrev Param := {r : ℝ // 0 < r} × ℝ
def raw (q : Param) : ℝ × ℝ := (q.1.val,q.2)
def Space.pparam (S : Space E) (ij : S.I × S.I) : Param := (⟨S.r,S.rpos⟩,(S.param ij).2)
def Space.pquad (S : Space E) (X : Param → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  ∑' ij, X (S.pparam ij)*Complex.normSq (S.coords Z ij)

def targetMap (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) :
    (E →L[ℂ] E) →ₗ[ℂ] ((Σ i, (S i).I × (S i).I) → ℂ) where
  toFun Z a := (Real.sqrt (w a.1):ℂ)*(S a.1).coords (L a.1 Z) a.2
  map_add' X Y := by ext a; simp [mul_add]
  map_smul' c X := by ext a; simp [mul_left_comm]

def diagram (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) :
    DiagonalForms.System Param (S₀.I × S₀.I) (Σ i, (S i).I × (S i).I) :=
  CenteredTests.system S₀.basis S₀.p S₀.pos S₀.sum.summable (h S₀.r) (h_pos S₀.rpos)
    S₀.pparam (⟨S₀.r,S₀.rpos⟩,0)
    (fun j => by simp [Space.pparam, Space.param, frequency])
    (fun a => (S a.1).pparam a.2) (targetMap S w L)

theorem targetMap_norm (S : Fin 2 → Space E) (w : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (Z : E →L[ℂ] E) (a : Σ i, (S i).I × (S i).I) :
    Complex.normSq (targetMap S w L Z a)=w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2) := by
  simp only [targetMap, LinearMap.coe_mk, AddHom.coe_mk, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (hw _)]

theorem diagram_comparison (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) (X : Param → ℝ)
    (hX : ∀ q, 0 ≤ X q)
    (hs : ∀ i Z, Summable (fun a => X ((S i).pparam a)*Complex.normSq ((S i).coords Z a)))
    (he : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      ∑ i, w i*(S i).pquad X (L i Z) ≤ S₀.pquad X Z) :
    (diagram S₀ S w L).Comparison X := by
  intro z s
  let Z := CenteredTests.realize S₀.basis S₀.p S₀.base S₀.base_pos z
  have hz : S₀.coords Z=z.val := CenteredTests.realize_entries S₀.basis S₀.p S₀.base S₀.base_pos z
  have hm : Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p :=
    CenteredTests.realize_mem S₀.basis S₀.p S₀.base S₀.base_pos z
  have hn (a : Σ i, (S i).I × (S i).I) : 0 ≤ X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2)) := mul_nonneg (hX _) (mul_nonneg (hw _) (Complex.normSq_nonneg _))
  have hsum : Summable (fun a : Σ i, (S i).I × (S i).I => X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) := by
    apply (summable_sigma_of_nonneg hn).mpr
    refine ⟨fun i => ?_, (hasSum_fintype _).summable⟩
    simpa only [mul_left_comm] using (hs i (L i Z)).mul_left (w i)
  have ht := Summable.sum_le_tsum s (fun a _ => hn a) hsum
  have hv : (∑' a : Σ i, (S i).I × (S i).I, X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) =
      ∑ i, w i*(S i).pquad X (L i Z) := by
    rw [hsum.tsum_sigma]
    simp only [tsum_fintype, Space.pquad, mul_left_comm (X _) (w _), tsum_mul_left]
  rw [hv] at ht
  have hh := ht.trans (he Z hm)
  change (∑ a ∈ s, X ((S a.1).pparam a.2)*Complex.normSq (targetMap S w L Z a)) ≤ _
  simp only [targetMap_norm S w hw L]
  convert! hh using 1
  simp only [sourceForm, Space.pquad, hz]
  rfl

def plusWeight (q : Param) : ℝ := Space.plus (raw q)
def minusWeight (q : Param) : ℝ := Space.minus (raw q)
def thermalWeight (q : Param) : ℝ := weight q.1.val q.2

theorem plusWeight_pos (q : Param) : 0 < plusWeight q :=
  mul_pos (mul_pos (one_div_pos.mpr (h_pos q.1.property)) (f_pos _)) (Real.exp_pos _)
theorem minusWeight_pos (q : Param) : 0 < minusWeight q :=
  mul_pos (mul_pos (one_div_pos.mpr (h_pos q.1.property)) (f_pos _)) (Real.exp_pos _)

theorem diagram_thermal (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (hp : (diagram S₀ S w L).Comparison plusWeight)
    (hm : (diagram S₀ S w L).Comparison minusWeight)
    (hr : (diagram S₀ S w L).Comparison (fun q => q.1.val))
    (hs : (diagram S₀ S w L).Comparison (fun q => q.1.val+1)) :
    (diagram S₀ S w L).Comparison thermalWeight := by
  have h₁ : (fun q : Param => (1/h q.1.val)*f (-h q.1.val/2)*Real.exp (-h q.1.val/2)) =
      (fun q => q.1.val) := funext (fun q => reference_plus q.1.property)
  have h₂ : (fun q : Param => (1/h q.1.val)*f (-h q.1.val/2)*Real.exp (-(-h q.1.val/2))) =
      (fun q => q.1.val+1) := funext (fun q => reference_minus q.1.property)
  have hh := four_weight_interpolation (diagram S₀ S w L)
    (fun q => 1/h q.1.val) (fun q => h q.1.val*q.2/2) (fun q => -h q.1.val/2)
    (fun q => one_div_pos.mpr (h_pos q.1.property)) hp hm (by rwa [h₁]) (by rwa [h₂])
  exact hh
end ThermalSpectral

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

theorem weight_bounds {r : ℝ} (hr : 0<r) (v : ℝ) :
    r ≤ weight r v ∧ weight r v ≤ r+1 := by
  have hh := weight_frequency_bounds hr (Real.exp_pos (h r*v)) (zero_lt_one : (0:ℝ)<1)
  have he : frequency r (Real.exp (h r*v)) 1=v := by
    simp only [frequency, Real.log_exp, Real.log_one, sub_zero]
    field_simp [(h_pos hr).ne']
  rwa [he] at hh

def lowerWeight (r : ℝ) : ℝ := sInf (Set.range (weight r))

theorem lowerWeight_bounds {r : ℝ} (hr : 0<r) :
    r ≤ lowerWeight r ∧ ∀ v, lowerWeight r ≤ weight r v := by
  have hb : BddBelow (Set.range (weight r)) := ⟨r,by rintro _ ⟨v,rfl⟩; exact (weight_bounds hr v).1⟩
  constructor
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨v,rfl⟩; exact (weight_bounds hr v).1)
  · intro v; exact csInf_le hb (Set.mem_range_self v)

theorem lowerWeight_pos {r : ℝ} (hr : 0<r) : 0<lowerWeight r :=
  lt_of_lt_of_le hr (lowerWeight_bounds hr).1

def mixtureConstant (r : ℝ) : ℝ := (Real.sqrt (h r*lowerWeight r))⁻¹

theorem mixtureConstant_pos {r : ℝ} (hr : 0<r) : 0 < mixtureConstant r :=
  inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (h_pos hr) (lowerWeight_pos hr)))

theorem mixtureConstant_sq {r : ℝ} (hr : 0<r) :
    mixtureConstant r^2=1/(h r*lowerWeight r) := by
  rw [mixtureConstant, inv_pow, Real.sq_sqrt (mul_pos (h_pos hr) (lowerWeight_pos hr)).le, one_div]

theorem BKM_weight_bound {r : ℝ} (hr : 0<r) (v : ℝ) :
    1/h r ≤ mixtureConstant r^2*weight r v := by
  rw [mixtureConstant_sq hr]
  have hh := (lowerWeight_bounds hr).2 v
  have he : (1/(h r*lowerWeight r))*weight r v=weight r v/(h r*lowerWeight r) := by ring
  rw [he]
  apply (div_le_div_iff₀ (h_pos hr) (mul_pos (h_pos hr) (lowerWeight_pos hr))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hh (h_pos hr).le]
end ThermalMetric

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

def observable : (E →L[ℂ] E) →ₗ[ℂ] lp (fun _ : S.I × S.I => ℂ) 2 :=
  observableMap S.basis S.p S.pos S.sum.summable S.r S.rpos

theorem observable_norm_sq (Z : E →L[ℂ] E) :
    ‖S.observable Z‖^2=S.pquad thermalWeight Z := by
  rw [observable, observableMap, LinearMap.coe_mk, AddHom.coe_mk, weightedVector_norm_sq]
  simp only [pquad, S.coords_norm, Complex.normSq_eq_norm_sq]
  apply tsum_congr
  intro a
  simp only [thermalWeight, pparam, param, base, metricCoefficient]
  ring

theorem thermal_summable (Z : E →L[ℂ] E) :
    Summable (fun ij => thermalWeight (S.pparam ij)*Complex.normSq (S.coords Z ij)) := by
  have hn (ij : S.I × S.I) : 0 ≤ thermalWeight (S.pparam ij)*Complex.normSq (S.coords Z ij) :=
    mul_nonneg (weight_pos S.rpos _).le (Complex.normSq_nonneg _)
  have hb (ij : S.I × S.I) :
      thermalWeight (S.pparam ij)*Complex.normSq (S.coords Z ij) ≤
        (S.r+1)*Complex.normSq (S.coords Z ij) := by
    have hh : thermalWeight (S.pparam ij) ≤ S.r+1 :=
      (weight_frequency_bounds S.rpos (S.pos ij.1) (S.pos ij.2)).2
    exact mul_le_mul_of_nonneg_right hh (Complex.normSq_nonneg _)
  exact Summable.of_nonneg_of_le hn hb (S.constant_summable (S.r+1) Z)

theorem BKM_thermal_bound (Z : E →L[ℂ] E) :
    S.pquad (fun _ => 1/h S.r) Z ≤ mixtureConstant S.r^2*‖S.observable Z‖^2 := by
  rw [S.observable_norm_sq]
  simp only [pquad, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro a
    have hh := BKM_weight_bound S.rpos (S.param a).2
    exact (mul_le_mul_of_nonneg_right hh (Complex.normSq_nonneg _)).trans_eq (mul_assoc _ _ _)
  · exact S.constant_summable (1/h S.r) Z
  · exact (S.thermal_summable Z).mul_left _

theorem observable_mem_core (Z : E →L[ℂ] E)
    (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    S.observable Z ∈ centeredSpace S.r S.rpos S.p S.pos S.sum.summable := by
  rw [← observable_core_dense S.basis S.p S.pos S.sum S.r S.rpos]
  exact Submodule.le_topologicalClosure _ ⟨Z,hZ,rfl⟩
end ThermalSpectral.Space

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def pairingLM (u v : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) : (E →L[ℂ] E) →ₗ[ℂ] ℂ where
  toFun := pairing u v
  map_add' Z T := by
    simp only [pairing, add_apply, inner_add_right]
    exact (pairing_summable hu hv Z).tsum_add (pairing_summable hu hv T)
  map_smul' c Z := by
    simp only [pairing, smul_apply, inner_smul_right, tsum_mul_left, smul_eq_mul, RingHom.id_apply]

omit [CompleteSpace E] in
theorem pairing_sub_right (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing u (fun i => v i-c • w i) Z=pairing u v Z-conj c*pairing u w Z := by
  simp only [pairing, inner_sub_left, inner_smul_left]
  rw [(pairing_summable hu hv Z).tsum_sub ((pairing_summable hu hw Z).mul_left (conj c)), tsum_mul_left]

omit [CompleteSpace E] in
theorem pairing_sub_left (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing (fun i => u i-c • v i) w Z=pairing u w Z-c*pairing v w Z := by
  simp only [pairing, map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [(pairing_summable hu hw Z).tsum_sub ((pairing_summable hv hw Z).mul_left c), tsum_mul_left]
end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation BeamLadder ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem centeredLadder_lower (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ false x=sandwich 0 3 (by omega) j x-μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [lowering_weighted_apply, single_lower_third_apply]

theorem centeredLadder_raise (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ true x=creationSandwich 0 3 (by omega) j x-conj μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, ↓reduceIte, ContinuousLinearMap.comp_apply, sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [raising_weighted_apply, single_raise_third_apply]
  by_cases hk : k j=0
  · simp only [hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul, ↓reduceIte]
  · rw [ite_eq_right hk]

theorem weakDefect_uncentered (t : ℝ) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (μ : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    weakDefect t x j μ Z=singleWeak t j x Z-conj μ*
      CrossEnsemble.pairing (fun r => inverseWeight 3 (x r)) (fun r => inverseWeight 3 (x r)) Z := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  simp only [weakDefect, centeredLadder_lower, centeredLadder_raise]
  rw [CrossEnsemble.pairing_sub_right _ _ _ hi hl hi,
    CrossEnsemble.pairing_sub_left _ _ _ hr hi hi]
  unfold singleWeak
  ring
end WeightedGenerator

namespace ThermalSpectral.Space
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

theorem defectFunctional_observable (x : S.I → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (S.p r):ℂ) • S.basis r)
    (j : Fin n) (μ : ℂ)
    (hd : Summable (fun a : S.I × S.I =>
      (1-frequency S.r (S.p a.1) (S.p a.2))*defectCoefficient S.r (S.p a.1) (S.p a.2)*
        ‖centeredEntry S.basis S.p x j μ a.1 a.2‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    defectFunctional S.r S.rpos S.p S.pos (fun a => centeredEntry S.basis S.p x j μ a.1 a.2) hd
        (S.observable Z)=weakDefect S.r x j μ Z := by
  exact (defectVector_pairing S.r S.rpos S.p S.pos _ hd
    (fun a => inner ℂ (S.basis a.1) (Z (S.basis a.2)))
    (observable_summable S.basis S.p S.pos S.sum.summable S.r S.rpos Z)).unique
      (weakDefect_spectral S.basis S.p S.pos x hx hi S.r j μ Z)

theorem defectFunctional_one (d : S.I × S.I → ℂ) (hd)
    (hc : HasSum (fun j => (S.p j:ℂ)*d (j,j)) 0) :
    defectFunctional S.r S.rpos S.p S.pos d hd (S.observable 1)=0 := by
  have hh := defectVector_mem_centeredSpace S.r S.rpos S.p S.pos S.sum.summable d hd hc
  change inner ℂ (identityVector S.r S.rpos S.p S.pos S.sum.summable)
    (defectVector S.r S.rpos S.p S.pos d hd)=0 at hh
  change inner ℂ (defectVector S.r S.rpos S.p S.pos d hd) (S.observable 1)=0
  have he : S.observable 1=identityVector S.r S.rpos S.p S.pos S.sum.summable :=
    observableMap_id S.basis S.p S.pos S.sum.summable S.r S.rpos
  rw [he, ← inner_conj_symm, hh, map_zero]

theorem weakDefect_centered {ρ : State n} (X : WeightedColumns ρ) (hI : X.Index=S.I)
    (x : S.I → Fock n) (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (S.p r):ℂ) • S.basis r)
    (he : HEq X.vector x) (j : Fin n) (μ : ℂ)
    (hd : Summable (fun a : S.I × S.I =>
      (1-frequency S.r (S.p a.1) (S.p a.2))*defectCoefficient S.r (S.p a.1) (S.p a.2)*
        ‖centeredEntry S.basis S.p x j μ a.1 a.2‖^2))
    (hc : HasSum (fun r => (S.p r:ℂ)*centeredEntry S.basis S.p x j μ r r) 0)
    (Z : Fock n →L[ℂ] Fock n) :
    weakDefect S.r x j μ Z=X.centeredWeak S.r j Z := by
  have hz : weakDefect S.r x j μ 1=0 := by
    rw [← S.defectFunctional_observable x hx hi j μ hd, S.defectFunctional_one _ hd hc]
  rcases X with ⟨I,v,hs,hn,heig⟩
  dsimp only at hI he ⊢
  subst I
  have hev : v=x := eq_of_heq he
  subst v
  have hm : BeamLadder.singleWeak S.r j x 1=conj μ := by
    rw [weakDefect_uncentered S.r x hx j μ 1] at hz
    have ht : CrossEnsemble.pairing (fun r => inverseWeight 3 (x r))
        (fun r => inverseWeight 3 (x r)) 1=1 :=
      (WeightedColumns.mk S.I x hs hn heig).expectation_one
    rw [ht, mul_one] at hz
    exact sub_eq_zero.mp hz
  rw [weakDefect_uncentered S.r x hx j μ Z]
  simp only [WeightedColumns.centeredWeak, WeightedColumns.weakMean, WeightedColumns.expectation, hm]
end ThermalSpectral.Space

end

end OAI
