import Mathlib
import OAI.Probability.LogConcave.Analysis.Poincare

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace Appell
open MeasureTheory
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

def HasGrowth (f : E → F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ x, ‖f x‖ ≤ C*(1+‖x‖^n)

lemma pow_le_one_add_pow_add {a : ℝ} (ha : 0 ≤ a) (n m : ℕ) :
    a^n ≤ 1+a^(n+m) := by
  by_cases h : a ≤ 1
  · exact (pow_le_one₀ ha h).trans (le_add_of_nonneg_right (by positivity))
  · have h' : 1 ≤ a := le_of_not_ge h
    have hp := mul_le_mul_of_nonneg_left (one_le_pow₀ h' : 1 ≤ a^m)
      (pow_nonneg ha n)
    rw [mul_one,← pow_add] at hp
    linarith

lemma HasGrowth.const (c : F) : HasGrowth (fun _ : E => c) := by
  exact ⟨‖c‖,norm_nonneg _,0,fun _ => by simp only [pow_zero]; nlinarith [norm_nonneg c]⟩

lemma HasGrowth.add {f g : E → F} (hf : HasGrowth f) (hg : HasGrowth g) :
    HasGrowth (fun x => f x+g x) := by
  obtain ⟨A,hA,n,hn⟩ := hf
  obtain ⟨B,hB,m,hm⟩ := hg
  refine ⟨2*(A+B),by positivity,n+m,fun x => ?_⟩
  have ha := pow_le_one_add_pow_add (norm_nonneg x) n m
  have hb := pow_le_one_add_pow_add (norm_nonneg x) m n
  rw [Nat.add_comm m n] at hb
  have h := (norm_add_le (f x) (g x)).trans (add_le_add (hn x) (hm x))
  nlinarith [mul_le_mul_of_nonneg_left ha hA,mul_le_mul_of_nonneg_left hb hB,
    mul_nonneg hA (pow_nonneg (norm_nonneg x) (n+m)),mul_nonneg hB (pow_nonneg (norm_nonneg x) (n+m))]

lemma HasGrowth.smul [NormedSpace ℝ F] {f : E → ℝ} {g : E → F}
    (hf : HasGrowth f) (hg : HasGrowth g) : HasGrowth (fun x => f x • g x) := by
  obtain ⟨A,hA,n,hn⟩ := hf
  obtain ⟨B,hB,m,hm⟩ := hg
  refine ⟨4*A*B,by positivity,n+m,fun x => ?_⟩
  rw [norm_smul]
  have h := mul_le_mul (hn x) (hm x) (norm_nonneg _) (by positivity)
  have ha := pow_le_one_add_pow_add (norm_nonneg x) n m
  have hb := pow_le_one_add_pow_add (norm_nonneg x) m n
  rw [Nat.add_comm m n] at hb
  have he : (1+‖x‖^n)*(1+‖x‖^m) ≤ 4*(1+‖x‖^(n+m)) := by
    rw [pow_add] at ha hb ⊢
    nlinarith [pow_nonneg (norm_nonneg x) n,pow_nonneg (norm_nonneg x) m]
  have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hA hB)
  nlinarith

lemma HasGrowth.mul {f g : E → ℝ} (hf : HasGrowth f) (hg : HasGrowth g) :
    HasGrowth (fun x => f x*g x) := hf.smul hg

lemma HasGrowth.norm {f : E → F} (hf : HasGrowth f) : HasGrowth (fun x => ‖f x‖) := by
  simpa only [HasGrowth,norm_norm] using hf

lemma HasGrowth.pow {f : E → ℝ} (hf : HasGrowth f) (n : ℕ) :
    HasGrowth (fun x => (f x)^n) := by
  induction n with
  | zero => simpa using HasGrowth.const (E := E) (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma HasGrowth.sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, HasGrowth (f i)) : HasGrowth (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasGrowth.const (E := E) (0:F)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasGrowth.prod {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, HasGrowth (f i)) : HasGrowth (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasGrowth.const (E := E) (1:ℝ)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasGrowth.linear [NormedSpace ℝ E] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    HasGrowth L := by
  refine ⟨‖L‖,norm_nonneg _,1,fun x => ?_⟩
  exact (L.le_opNorm x).trans (by simp only [pow_one]; nlinarith [norm_nonneg L])

lemma HasGrowth.lipschitz {K : ℝ≥0} {f : E → F} (hf : LipschitzWith K f) : HasGrowth f := by
  refine ⟨(K:ℝ)+‖f 0‖,by positivity,1,fun x => ?_⟩
  have hh := hf.dist_le_mul x 0
  rw [dist_eq_norm,dist_zero_right] at hh
  simp only [pow_one]
  nlinarith [norm_le_norm_sub_add (f x) (f 0),mul_nonneg (norm_nonneg (f 0)) (norm_nonneg x)]

variable [MeasurableSpace E]

def HasMoments (μ : Measure E) : Prop := ∀ n : ℕ, Integrable (fun x : E => ‖x‖^n) μ

lemma HasGrowth.integrable {μ : Measure E} [IsFiniteMeasure μ] {f : E → F}
    (hf : HasGrowth f) (hm : AEStronglyMeasurable f μ) (hμ : HasMoments μ) : Integrable f μ := by
  obtain ⟨C,hC,n,hn⟩ := hf
  exact (((integrable_const (1:ℝ)).add (hμ n)).const_mul C).mono' hm
    (Filter.Eventually.of_forall hn)

lemma HasGrowth.memLp {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : HasGrowth f) (hm : AEStronglyMeasurable f μ) (hμ : HasMoments μ) : MemLp f 2 μ := by
  exact (memLp_two_iff_integrable_sq hm).2 ((hf.pow 2).integrable (hm.pow 2) hμ)

end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

variable {ι : Type*} [DecidableEq ι]

def inverseMoment (m : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  if _hs : s = ∅ then 1 else
    -∑ t ∈ (s.powerset.filter (fun t => t ≠ s)).attach, m (s \ t.1)*inverseMoment m t.1
termination_by s.card
decreasing_by
  have ht := (Finset.mem_filter.mp t.2)
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.mem_powerset.mp ht.1,ht.2⟩)

@[simp] lemma inverseMoment_empty (m : Finset ι → ℝ) : inverseMoment m ∅ = 1 := by
  rw [inverseMoment]
  simp

lemma inverseMoment_convolution (m : Finset ι → ℝ) (hm : m ∅ = 1) (s : Finset ι) :
    ∑ t ∈ s.powerset, m (s \ t)*inverseMoment m t = if s = ∅ then 1 else 0 := by
  by_cases hs : s = ∅
  · subst s
    simp [hm]
  have hmem : s ∈ s.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl s)
  have he : s.powerset.filter (fun t => t ≠ s) = s.powerset.erase s := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_erase]
    tauto
  have hi := inverseMoment.eq_def m s
  simp only [hs,↓reduceDIte] at hi
  change inverseMoment m s = -∑ t ∈ (s.powerset.filter (fun t => t ≠ s)).attach,
    (fun t => m (s \ t)*inverseMoment m t) t.1 at hi
  have hat := Finset.sum_attach (s.powerset.filter (fun t => t ≠ s))
    (fun t => m (s \ t)*inverseMoment m t)
  rw [hat,he] at hi
  rw [ite_eq_right hs,← Finset.sum_erase_add _ _ hmem]
  simp only [Finset.sdiff_self,hm,one_mul]
  linarith

lemma inverseMoment_nonempty (m : Finset ι → ℝ) {s : Finset ι} (hs : s ≠ ∅) :
    inverseMoment m s = -∑ t ∈ s.powerset.erase s, m (s \ t)*inverseMoment m t := by
  have h := inverseMoment.eq_def m s
  simp only [hs,↓reduceDIte] at h
  have hat := Finset.sum_attach (s.powerset.filter (fun t => t ≠ s))
    (fun t => m (s \ t)*inverseMoment m t)
  rw [hat] at h
  convert! h using 2
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [Finset.mem_filter,Finset.mem_erase]
  tauto

lemma inverseMoment_image {κ : Type*} [DecidableEq κ] (e : ι → κ)
    (he : Function.Injective e) (m : Finset κ → ℝ) (s : Finset ι) :
    inverseMoment (fun t => m (t.image e)) s = inverseMoment m (s.image e) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s; simp
    have hs' : s.image e ≠ ∅ := by simpa using hs
    rw [inverseMoment_nonempty _ hs,inverseMoment_nonempty _ hs']
    have hi : Function.Injective (fun t : Finset ι => t.image e) := Finset.image_injective he
    have hp : (s.image e).powerset.erase (s.image e) =
        (s.powerset.erase s).image (fun t => t.image e) := by
      rw [Finset.powerset_image,← Finset.image_erase hi]
    rw [hp,Finset.sum_image]
    · congr 1
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.image_sdiff _ _ he,
        ih t (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2,
          (Finset.mem_erase.mp ht).1⟩)]
    · exact fun _ _ _ _ h => hi h

def polynomial (m : Finset ι → ℝ) (s : Finset ι) (z : ι → ℝ) : ℝ :=
  ∑ t ∈ s.powerset, inverseMoment m t * ∏ i ∈ s \ t, z i

@[simp] lemma polynomial_empty (m : Finset ι → ℝ) (z : ι → ℝ) : polynomial m ∅ z = 1 := by
  simp [polynomial]

lemma polynomial_image {κ : Type*} [DecidableEq κ] (e : ι → κ)
    (he : Function.Injective e) (m : Finset κ → ℝ) (s : Finset ι) (z : κ → ℝ) :
    polynomial (fun t => m (t.image e)) s (z ∘ e) = polynomial m (s.image e) z := by
  rw [polynomial,polynomial,Finset.powerset_image,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [inverseMoment_image e he m,← Finset.image_sdiff _ _ he,Finset.prod_image]
    · rfl
    · exact fun _ _ _ _ h => he h
  · exact fun _ _ _ _ h => Finset.image_injective he h

def moments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ι → Ω → ℝ)
    (s : Finset ι) : ℝ := ∫ ω, ∏ i ∈ s, X i ω ∂μ

omit [DecidableEq ι] in
lemma moments_empty {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) : moments μ X ∅ = 1 := by simp [moments]

omit [DecidableEq ι] in
lemma moments_image {Ω κ : Type*} [MeasurableSpace Ω] [DecidableEq κ]
    (μ : Measure Ω) (X : κ → Ω → ℝ) (e : ι → κ) (he : Function.Injective e) (s : Finset ι) :
    moments μ (X ∘ e) s = moments μ X (s.image e) := by
  unfold moments
  congr 1
  funext ω
  rw [Finset.prod_image]
  · rfl
  · exact fun _ _ _ _ h => he h

lemma polynomial_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ t ⊆ s, Integrable (fun ω => ∏ i ∈ t, X i ω) μ) (m : Finset ι → ℝ) :
    Integrable (fun ω => polynomial m s (fun i => X i ω)) μ := by
  apply integrable_finsetSum
  intro t ht
  exact (hX (s \ t) Finset.sdiff_subset).const_mul _

lemma integral_polynomial {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (s : Finset ι)
    (hX : ∀ t ⊆ s, Integrable (fun ω => ∏ i ∈ t, X i ω) μ) :
    (∫ ω, polynomial (moments μ X) s (fun i => X i ω) ∂μ) = if s = ∅ then 1 else 0 := by
  simp only [polynomial]
  rw [integral_finsetSum _ (fun t ht => (hX (s \ t) Finset.sdiff_subset).const_mul _)]
  simp only [integral_const_mul]
  simpa only [moments,mul_comm] using inverseMoment_convolution (moments μ X) (moments_empty μ X) s

lemma sum_powerset_sdiff {M : Type*} [AddCommMonoid M] (s : Finset ι)
    (F : ι → Finset ι → M) :
    (∑ t ∈ s.powerset, ∑ i ∈ s \ t, F i t) =
      ∑ i ∈ s, ∑ t ∈ (s.erase i).powerset, F i t := by
  have hsd (t : Finset ι) : ∑ i ∈ s \ t, F i t = ∑ i ∈ s, if i ∉ t then F i t else 0 := by
    have he : s \ t = s.filter (fun i => i ∉ t) := by ext i; simp
    rw [he,Finset.sum_filter]
  simp_rw [hsd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t
  simp only [Finset.mem_filter,Finset.mem_powerset,Finset.subset_erase]

section Derivatives
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma polynomial_contDiff (m : Finset ι → ℝ) (s : Finset ι) (a : ι → E →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : E => polynomial m s (fun i => a i z)) := by
  unfold polynomial
  apply ContDiff.sum
  intro t ht
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact (a i).contDiff

lemma hasFDerivAt_polynomial (m : Finset ι → ℝ) (s : Finset ι)
    (a : ι → E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun z : E => polynomial m s (fun i => a i z))
      (∑ i ∈ s, polynomial m (s.erase i) (fun j => a j x) • a i) x := by
  have hd : HasFDerivAt (fun z : E => polynomial m s (fun i => a i z))
      (∑ t ∈ s.powerset, inverseMoment m t •
        ∑ i ∈ s \ t, (∏ j ∈ (s \ t).erase i, a j x) • a i) x := by
    apply HasFDerivAt.fun_sum
    intro t ht
    exact (HasFDerivAt.finsetProd (fun i hi => (a i).hasFDerivAt)).const_mul _
  apply hd.congr_fderiv
  simp only [Finset.smul_sum,smul_smul]
  have hset (i : ι) (t : Finset ι) : (s \ t).erase i = s.erase i \ t := by
    ext j
    simp only [Finset.mem_erase,Finset.mem_sdiff]
    tauto
  simp_rw [hset]
  rw [sum_powerset_sdiff]
  simp only [polynomial,Finset.sum_smul]

end Derivatives
end Appell
end LogConcaveSampling

namespace LogConcaveSampling
namespace Appell
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def coordinate (b : OrthonormalBasis κ ℝ E) (i : κ) : E →L[ℝ] ℝ := innerSL ℝ (b i)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma coordinate_basis (b : OrthonormalBasis κ ℝ E) (i j : κ) :
    coordinate b i (b j) = if i = j then 1 else 0 := by
  exact orthonormal_iff_ite.mp b.orthonormal i j

def slotPolynomial (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (s : Finset ι) (x : E) : ℝ :=
  polynomial (moments μ (fun i => coordinate b (a i))) s (fun i => coordinate b (a i) x)

def tensorPolynomial (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) : ℝ :=
  ∑ a, T a * slotPolynomial μ b a Finset.univ x

omit [MeasurableSpace E] [BorelSpace E] in
lemma growth_polynomial {J : Type*} [DecidableEq J] (m : Finset J → ℝ)
    (s : Finset J) (a : J → E →L[ℝ] ℝ) :
    HasGrowth (fun x => polynomial m s (fun i => a i x)) := by
  exact HasGrowth.sum _ (fun t ht => (HasGrowth.const _).mul
    (HasGrowth.prod _ (fun i hi => HasGrowth.linear (a i))))

omit [BorelSpace E] [Fintype ι] [DecidableEq κ] in
lemma slotPolynomial_growth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (s : Finset ι) : HasGrowth (slotPolynomial μ b a s) :=
  growth_polynomial _ _ _

omit [DecidableEq κ] in
omit [BorelSpace E] in
lemma tensorPolynomial_growth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) : HasGrowth (tensorPolynomial μ b T) :=
  HasGrowth.sum _ (fun a _ha => (HasGrowth.const _).mul (slotPolynomial_growth μ b a _))

omit [BorelSpace E] [Fintype ι] [DecidableEq κ] in
lemma slotPolynomial_smooth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (s : Finset ι) : ContDiff ℝ (⊤ : ℕ∞) (slotPolynomial μ b a s) :=
  polynomial_contDiff _ _ _

omit [BorelSpace E] [DecidableEq κ] in
lemma tensorPolynomial_smooth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (tensorPolynomial μ b T) :=
  ContDiff.sum (fun a _ha => contDiff_const.mul (slotPolynomial_smooth μ b a _))

omit [Fintype ι] [DecidableEq κ] in
lemma integral_slotPolynomial (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (a : ι → κ) (s : Finset ι) :
    (∫ x, slotPolynomial μ b a s x ∂μ) = if s = ∅ then 1 else 0 := by
  apply integral_polynomial
  intro t ht
  exact (HasGrowth.prod t (fun i hi => HasGrowth.linear (coordinate b (a i)))).integrable
    (continuous_finsetProd _ (fun i hi => (coordinate b (a i)).continuous)).aestronglyMeasurable hμ

omit [DecidableEq κ] in
lemma integral_tensorPolynomial (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) [Nonempty ι] :
    (∫ x, tensorPolynomial μ b T x ∂μ) = 0 := by
  simp only [tensorPolynomial]
  rw [integral_finsetSum]
  · simp only [integral_const_mul,integral_slotPolynomial μ hμ,
      Finset.univ_eq_empty_iff,not_isEmpty_of_nonempty,↓reduceIte,mul_zero,Finset.sum_const_zero]
  · intro a ha
    exact ((slotPolynomial_growth μ b a _).integrable
      (slotPolynomial_smooth μ b a _).continuous.aestronglyMeasurable hμ).const_mul _

omit [BorelSpace E] [DecidableEq κ] in
lemma slotPolynomial_erase (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (a : ι → κ) (i : ι) (x : E) :
    slotPolynomial μ b a (Finset.univ.erase i) x =
      slotPolynomial μ b (fun j : {j // j ≠ i} => a j) Finset.univ x := by
  have he : (Finset.univ : Finset {j : ι // j ≠ i}).image Subtype.val = Finset.univ.erase i := by
    ext j
    simp
  have hm : moments μ (fun j : {j : ι // j ≠ i} => coordinate b (a j)) =
      fun t => moments μ (fun j : ι => coordinate b (a j)) (t.image Subtype.val) := by
    funext t
    exact moments_image μ (fun j : ι => coordinate b (a j)) Subtype.val Subtype.val_injective t
  unfold slotPolynomial
  rw [hm]
  simpa only [Function.comp_def,he] using
    (polynomial_image (fun j : {j : ι // j ≠ i} => j.val) Subtype.val_injective
      (moments μ (fun j : ι => coordinate b (a j))) Finset.univ
      (fun j => coordinate b (a j) x)).symm

def slice (T : (ι → κ) → ℝ) (i : ι) (k : κ) (a : {j // j ≠ i} → κ) : ℝ :=
  T ((Equiv.piSplitAt i (fun _ => κ)).symm (k,a))

omit [BorelSpace E] [DecidableEq κ] in
lemma hasFDerivAt_tensorPolynomial (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) :
    HasFDerivAt (tensorPolynomial μ b T)
      (∑ a, T a • ∑ i, slotPolynomial μ b a (Finset.univ.erase i) x • coordinate b (a i)) x := by
  exact HasFDerivAt.fun_sum (fun a _ha => (hasFDerivAt_polynomial _ _ _ x).const_mul (T a))

omit [BorelSpace E] in
lemma derivative_tensorPolynomial_basis (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) (k : κ) :
    fderiv ℝ (tensorPolynomial μ b T) x (b k) =
      ∑ i, tensorPolynomial μ b (slice T i k) x := by
  rw [(hasFDerivAt_tensorPolynomial μ b T x).fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul,
    coordinate_basis,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (Equiv.piSplitAt i (fun _ => κ)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.piSplitAt_symm_apply,dite_true]
  simp only [mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold tensorPolynomial
  apply Finset.sum_congr rfl
  intro a ha
  rw [slotPolynomial_erase]
  congr 1
  congr 1
  funext j
  simp [Equiv.piSplitAt_symm_apply,j.prop]

omit [DecidableEq κ] in
lemma tensorPolynomial_memLp (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) :
    MemLp (tensorPolynomial μ b T) 2 μ :=
  (tensorPolynomial_growth μ b T).memLp
    (tensorPolynomial_smooth μ b T).continuous.aestronglyMeasurable hμ

omit [DecidableEq κ] in
omit [BorelSpace E] in
lemma tensorPolynomial_derivative_growth (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) : HasGrowth (fun x => fderiv ℝ (tensorPolynomial μ b T) x) := by
  simp only [(hasFDerivAt_tensorPolynomial μ b T _).fderiv]
  exact HasGrowth.sum _ (fun a _ha => (HasGrowth.const _).smul
    (HasGrowth.sum _ (fun i _hi => (slotPolynomial_growth μ b a _).smul (HasGrowth.const _))))

omit [DecidableEq κ] in
lemma tensorPolynomial_derivative_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : HasMoments μ) (b : OrthonormalBasis κ ℝ E) (T : (ι → κ) → ℝ) :
    Integrable (fun x => ‖fderiv ℝ (tensorPolynomial μ b T) x‖^2) μ := by
  have hd : Continuous (fun x => fderiv ℝ (tensorPolynomial μ b T) x) :=
    (tensorPolynomial_smooth μ b T).continuous_fderiv (by simp)
  exact ((tensorPolynomial_derivative_growth μ b T).norm.pow 2).integrable
    (hd.norm.pow 2).aestronglyMeasurable hμ

omit [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
lemma sq_sum_le_card_mul_sum_sq (f : ι → ℝ) :
    (∑ i, f i)^2 ≤ (Fintype.card ι:ℝ)*∑ i, (f i)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1:ℝ)) f

omit [BorelSpace E] in
lemma tensorPolynomial_derivative_bound (μ : Measure E) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) (x : E) :
    ‖fderiv ℝ (tensorPolynomial μ b T) x‖^2 ≤
      (Fintype.card ι:ℝ)*∑ i, ∑ k, (tensorPolynomial μ b (slice T i k) x)^2 := by
  rw [b.norm_dual]
  simp_rw [derivative_tensorPolynomial_basis μ b T]
  calc
    _ ≤ ∑ k, (Fintype.card ι:ℝ)*∑ i, (tensorPolynomial μ b (slice T i k) x)^2 :=
      Finset.sum_le_sum (fun k hk => sq_sum_le_card_mul_sum_sq _)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

lemma tensorPolynomial_one_step (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) [Nonempty ι] :
    (∫ x, (tensorPolynomial μ b T x)^2 ∂μ) ≤
      β*(Fintype.card ι:ℝ)*∑ i, ∑ k, ∫ x, (tensorPolynomial μ b (slice T i k) x)^2 ∂μ := by
  have hi (i : ι) (k : κ) : Integrable (fun x => (tensorPolynomial μ b (slice T i k) x)^2) μ :=
    (tensorPolynomial_memLp μ hμ b _).integrable_sq
  have hp := hP _ ((tensorPolynomial_smooth μ b T).of_le (by simp))
    (tensorPolynomial_memLp μ hμ b T) (tensorPolynomial_derivative_integrable μ hμ b T)
  rw [variance_eq_sub (tensorPolynomial_memLp μ hμ b T),integral_tensorPolynomial μ hμ,
    zero_pow (by norm_num : 2 ≠ 0),sub_zero] at hp
  have hh := integral_mono (tensorPolynomial_derivative_integrable μ hμ b T)
    ((integrable_finsetSum _ (fun i hi' => integrable_finsetSum _ (fun k hk => hi i k))).const_mul
      (Fintype.card ι:ℝ)) (tensorPolynomial_derivative_bound μ b T)
  rw [integral_const_mul,integral_finsetSum] at hh
  · simp_rw [integral_finsetSum _ (fun k hk => hi _ k)] at hh
    exact hp.trans ((mul_le_mul_of_nonneg_left hh hβ).trans_eq (by ring))
  · intro i hi'
    exact integrable_finsetSum _ (fun k hk => hi i k)

omit [MeasurableSpace E] [BorelSpace E] [DecidableEq κ] in
lemma slice_energy (T : (ι → κ) → ℝ) (i : ι) :
    (∑ k, ∑ a, (slice T i k a)^2) = ∑ a, (T a)^2 := by
  simpa only [slice,Fintype.sum_prod_type] using
    (Equiv.piSplitAt i (fun _ => κ)).symm.sum_comp (fun a => (T a)^2)

universe u

theorem tensorPolynomial_L2_aux (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (n : ℕ) : ∀ (J : Type u) [Fintype J] [DecidableEq J], Fintype.card J = n →
      ∀ T : (J → κ) → ℝ,
      (∫ x, (tensorPolynomial μ b T x)^2 ∂μ) ≤
        β^n*(n.factorial:ℝ)^2*∑ a, (T a)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ _ hc T
    by_cases hn : n = 0
    · have : IsEmpty J := Fintype.card_eq_zero_iff.mp (hc.trans hn)
      let a : J → κ := fun j => isEmptyElim j
      let : Unique (J → κ) := ⟨⟨a⟩,fun f => funext (fun j => isEmptyElim j)⟩
      simp [hn,tensorPolynomial,slotPolynomial]
    have hp : 0 < n := Nat.pos_of_ne_zero hn
    have : Nonempty J := Fintype.card_pos_iff.mp (hc ▸ hp)
    have hcard (i : J) : Fintype.card {j : J // j ≠ i} = n-1 := by
      rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,hc]
    let C : ℝ := β^(n-1)*((n-1).factorial:ℝ)^2
    have hb (i : J) (k : κ) :
        (∫ x, (tensorPolynomial μ b (slice T i k) x)^2 ∂μ) ≤
          C*∑ a, (slice T i k a)^2 :=
      ih (n-1) (Nat.sub_lt hp (by norm_num)) _ (hcard i) (slice T i k)
    have hh := (tensorPolynomial_one_step μ hμ hβ hP b T).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i hi =>
        Finset.sum_le_sum (fun k hk => hb i k))) (mul_nonneg hβ (Nat.cast_nonneg (Fintype.card J))))
    have he : (∑ i, ∑ k, C*∑ a, (slice T i k a)^2) = C*(n:ℝ)*∑ a, (T a)^2 := by
      simp_rw [← Finset.mul_sum,slice_energy]
      simp only [Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul]
      ring
    rw [he] at hh
    have hn' : n-1+1=n := Nat.sub_add_cancel hp
    have hf : (n.factorial:ℝ) = (n:ℝ)*((n-1).factorial:ℝ) := by
      have hf' := Nat.factorial_succ (n-1)
      rw [hn'] at hf'
      exact_mod_cast hf'
    have hpow : β^n=β^(n-1)*β := by
      calc β^n = β^(n-1+1) := congrArg (fun j => β^j) hn'.symm
           _ = β^(n-1)*β := pow_succ _ _
    convert! hh using 1
    rw [hc,hf,hpow]
    dsimp [C]
    ring

theorem tensorPolynomial_L2 (μ : Measure E) [IsProbabilityMeasure μ] (hμ : HasMoments μ)
    {β : ℝ} (hβ : 0 ≤ β) (hP : HasPoincare μ β) (b : OrthonormalBasis κ ℝ E)
    (T : (ι → κ) → ℝ) :
    (∫ x, (tensorPolynomial μ b T x)^2 ∂μ) ≤
      β^(Fintype.card ι)*((Fintype.card ι).factorial:ℝ)^2*∑ a, (T a)^2 :=
  tensorPolynomial_L2_aux μ hμ hβ hP b _ ι rfl T

end Appell
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
