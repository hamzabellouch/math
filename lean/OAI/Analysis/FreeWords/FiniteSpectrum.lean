import Mathlib
import OAI.Analysis.FreeWords.SpectralCuts

namespace OAI

noncomputable section

namespace KKSpectralSupport

open KKTraceTransfer KKPolarSupport

open scoped InnerProductSpace ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

variable {M : VonNeumannAlgebra H}

theorem spectralBand_mul_cut (a : ConcreteAlgebra M) {s t v : ℝ} (hst : s ≤ t) (htv : t ≤ v) :
    spectralBand a s t*spectralCut a v=0 := by
  rw [spectralBand,sub_mul,
    ((spectralCut_isProjection a v).le_iff_mul_eq_right (spectralCut_isProjection a s)).mp (spectralCut_antitone a (hst.trans htv)),
    ((spectralCut_isProjection a v).le_iff_mul_eq_right (spectralCut_isProjection a t)).mp (spectralCut_antitone a htv),sub_self]

theorem spectralBand_orthogonal (a : ConcreteAlgebra M) {s t v w : ℝ}
    (hst : s ≤ t) (htv : t ≤ v) (hvw : v ≤ w) : spectralBand a s t*spectralBand a v w=0 := by
  change spectralBand a s t*(spectralCut a v-spectralCut a w)=0
  rw [mul_sub,spectralBand_mul_cut a hst htv,
    spectralBand_mul_cut a hst (htv.trans hvw),sub_self]

theorem partition_error_bound {ι : Type*} [Fintype ι] (a : ConcreteAlgebra M)
    (p : ι → ConcreteAlgebra M) (c : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsum : ∑ i, p i=1)
    (hlow : ∀ i, 0 ≤ (a-algebraMap ℝ (ConcreteAlgebra M) (c i))*p i)
    (hupp : ∀ i, 0 ≤ (algebraMap ℝ (ConcreteAlgebra M) (c i+δ)-a)*p i) :
    ‖a-∑ i, (c i : ℂ) • p i‖ ≤ δ := by
  classical
  have he : a-∑ i, (c i : ℂ) • p i = ∑ i, (a-algebraMap ℝ (ConcreteAlgebra M) (c i))*p i := by
    simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum,hsum,mul_one,
      ← Algebra.smul_def,Complex.coe_smul]
  have hpos : 0 ≤ a-∑ i, (c i : ℂ) • p i := by
    rw [he]
    exact Finset.sum_nonneg (fun i hi => hlow i)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hδ hpos).mpr
  rw [he]
  calc
    _ ≤ ∑ i, algebraMap ℝ (ConcreteAlgebra M) δ*p i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hupp i
      rw [map_add] at h
      have hh : (algebraMap ℝ (ConcreteAlgebra M) (c i)+algebraMap ℝ (ConcreteAlgebra M) δ-a)*p i =
          algebraMap ℝ (ConcreteAlgebra M) δ*p i-(a-algebraMap ℝ (ConcreteAlgebra M) (c i))*p i := by noncomm_ring
      apply sub_nonneg.mp
      rw [← hh]
      exact h
    _ = _ := by rw [← Finset.mul_sum,hsum,mul_one]

theorem finite_spectrum_approximation_central (M : VonNeumannAlgebra H)
    (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (p : Fin n → ConcreteAlgebra M) (c : Fin n → ℝ),
      (∀ i, IsStarProjection (p i)) ∧ (∀ i j, i ≠ j → p i*p j=0) ∧
      (∑ i, p i=1) ∧ (∀ i, Commute a (p i)) ∧
      (∀ b, Commute b a → ∀ i, Commute b (p i)) ∧
      ‖a - ∑ i, (c i : ℂ) • p i‖ < ε := by
  classical
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  let B := ‖a‖+1
  obtain ⟨n,hn⟩ := exists_nat_gt ((2*B)/δ)
  have hnB : 2*B < (n:ℝ)*δ := (div_lt_iff₀ hδ).mp hn
  let t : ℕ → ℝ := fun i => -B+(i:ℝ)*δ
  have ht : Monotone t := by
    intro i j hij
    dsimp [t]
    exact add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hδ.le) _
  let p : Fin n → ConcreteAlgebra M := fun i => spectralBand a (t i) (t (i+1))
  have hp (i : Fin n) : IsStarProjection (p i) := spectralBand_isProjection a (ht (Nat.le_succ i))
  have hq0 : spectralCut a (t 0)=1 := spectralCut_eq_one a ha (by dsimp [t,B]; simp only [Nat.cast_zero,zero_mul,add_zero]; linarith)
  have hqn : spectralCut a (t n)=0 := spectralCut_eq_zero a (by dsimp [t,B] at *; linarith)
  have hsum : ∑ i, p i=1 := by
    change ∑ i : Fin n, (spectralCut a (t i)-spectralCut a (t (i+1)))=1
    rw [Fin.sum_univ_eq_sum_range (fun i => spectralCut a (t i)-spectralCut a (t (i+1))) n,
      Finset.sum_range_sub',hq0,hqn,sub_zero]
  refine ⟨n,p,(fun i => t i),hp,?_,hsum,(fun i => spectralBand_commute a ha _ _),?_,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact spectralBand_orthogonal a (ht (Nat.le_succ i)) (ht (Nat.succ_le_of_lt hij)) (ht (Nat.le_succ j))
    · have h := spectralBand_orthogonal a (ht (Nat.le_succ j)) (ht (Nat.succ_le_of_lt hji)) (ht (Nat.le_succ i))
      change p j*p i=0 at h
      simpa only [star_mul,(hp i).isSelfAdjoint.star_eq,(hp j).isSelfAdjoint.star_eq,star_zero] using congrArg star h
  · intro b hba i
    exact (spectralCut_commute_of_commute ha hba _).sub_right (spectralCut_commute_of_commute ha hba _)
  · apply lt_of_le_of_lt (partition_error_bound a p (fun i => t i) hδ.le hsum ?_ ?_) (by dsimp [δ]; linarith)
    · intro i
      exact spectralBand_lower a ha (ht (Nat.le_succ i))
    · intro i
      have hid : t i+δ=t (i+1) := by dsimp [t]; push_cast; ring
      rw [hid]
      exact spectralBand_upper a ha (ht (Nat.le_succ i))

theorem finite_spectrum_approximation (M : VonNeumannAlgebra H)
    (a : ConcreteAlgebra M) (ha : IsSelfAdjoint a) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (p : Fin n → ConcreteAlgebra M) (c : Fin n → ℝ),
      (∀ i, IsStarProjection (p i)) ∧ (∀ i j, i ≠ j → p i*p j=0) ∧
      (∑ i, p i=1) ∧ (∀ i, Commute a (p i)) ∧
      ‖a - ∑ i, (c i : ℂ) • p i‖ < ε := by
  obtain ⟨n,p,c,hp,ho,h1,hc,_,he⟩ := finite_spectrum_approximation_central M a ha ε hε
  exact ⟨n,p,c,hp,ho,h1,hc,he⟩

end

end KKSpectralSupport
end

end OAI
