import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

lemma JointSmooth.sum {v : ι → Field F} (hv : ∀ i, JointSmooth (v i)) :
    JointSmooth (fun t x => ∑ i, v i t x) := by
  exact ContDiff.sum (fun i _ => hv i)

lemma div_sum {v : ι → Velocity} (hv : ∀ i, JointSmooth (v i)) (t : ℝ) (x : Space) :
    div (fun t x => ∑ i, v i t x) t x = ∑ i, div (v i) t x := by
  have hd (i : ι) := ((hv i).slice t).differentiable (by simp) x
  simp only [div, spaceD, fderiv_fun_sum (fun i _ => hd i), sum_apply,
    Finset.sum_apply]
  exact Finset.sum_comm

def familyVelocity (a b : ι → Space) (c d : ι → ℝ → Space) (η : ℝ) : Velocity :=
  fun t x => ∑ i, movingBoxVelocity (a i) (b i) (c i) (d i) η t x

lemma familyVelocity_jointSmooth {c d : ι → ℝ → Space}
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hn : ∀ i t j, d i t j ≠ 0) (a b : ι → Space) (η : ℝ) :
    JointSmooth (familyVelocity a b c d η) :=
  JointSmooth.sum (fun i => movingBoxVelocity_jointSmooth (hc i) (hd i) (hn i) (a i) (b i) η)

lemma familyVelocity_divergence {c d : ι → ℝ → Space}
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hn : ∀ i t j, d i t j ≠ 0) (a b : ι → Space) (η t : ℝ) (x : Space) :
    div (familyVelocity a b c d η) t x = 0 := by
  change div (fun t x => ∑ i, movingBoxVelocity (a i) (b i) (c i) (d i) η t x) t x = 0
  rw [div_sum
    (fun i => movingBoxVelocity_jointSmooth (hc i) (hd i) (hn i) (a i) (b i) η)]
  exact Finset.sum_eq_zero (fun i _ =>
    movingBoxVelocity_divergence (hc i) (hd i) (hn i) (a i) (b i) η t x)

lemma tsupport_familyVelocity_subset (a b : ι → Space) (c d : ι → ℝ → Space)
    {η : ℝ} (hη : 0 < η) (t : ℝ) :
    tsupport (familyVelocity a b c d η t) ⊆
      ⋃ i, closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun _ => isCompact_Icc.isClosed))
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  apply image_eq_zero_of_notMem_tsupport
  intro hi
  exact hn (mem_iUnion.mpr ⟨i,
    tsupport_movingBoxVelocity_subset (a i) (b i) (c i) (d i) hη t hi⟩)

lemma openEnlargement_subset_closedEnlargement {a b : Space} {η δ : ℝ}
    (h : η ≤ δ) : openEnlargement a b η ⊆ closedEnlargement a b δ := by
  intro x hx
  rw [mem_openEnlargement] at hx
  rw [mem_closedEnlargement]
  intro i
  constructor <;> linarith [(hx i).1, (hx i).2]

lemma familyVelocity_eq_on_plateau {a b : ι → Space} {c d : ι → ℝ → Space}
    {η t : ℝ} (hη : 0 < η) (i : ι) {x : Space}
    (hx : x ∈ openEnlargement (lowerEndpoint (a i) (c i) (d i) t)
      (lowerEndpoint (b i) (c i) (d i) t) η)
    (hsep : Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (a j) (c j) (d j) t)
        (lowerEndpoint (b j) (c j) (d j) t) (2 * η))) :
    familyVelocity a b c d η t x = movingBoxVelocity (a i) (b i) (c i) (d i) η t x := by
  apply Finset.sum_eq_single i
  · intro j _ hji
    apply image_eq_zero_of_notMem_tsupport
    intro hxj
    exact Set.disjoint_left.mp (hsep (Ne.symm hji))
      (openEnlargement_subset_closedEnlargement (by linarith) hx)
      (tsupport_movingBoxVelocity_subset (a j) (b j) (c j) (d j) hη t hxj)
  · simp

theorem familyVelocity_affinePath {a b : ι → Space} {c d : ι → ℝ → Space}
    {η δ : ℝ} (hη : 0 < η)
    (hc : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i))
    (hd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (d i))
    (hp : ∀ i t j, 0 < d i t j) (hdet : ∀ i t, ∏ j, d i t j = 1)
    (i : ι) {z : Space} (hz : z ∈ openEnlargement (a i) (b i) δ) (t : ℝ)
    (hscale : ∀ j, d i t j * δ ≤ η)
    (hsep : Pairwise fun i j => Disjoint
      (closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η))
      (closedEnlargement (lowerEndpoint (a j) (c j) (d j) t)
        (lowerEndpoint (b j) (c j) (d j) t) (2 * η))) :
    HasDerivAt (affinePath (c i) (d i) z)
      (familyVelocity a b c d η t (affinePath (c i) (d i) z t)) t := by
  rw [familyVelocity_eq_on_plateau hη i
    (affinePath_mem_plateau_of_scaled_bound hz (hp i t) hscale) hsep]
  exact affinePath_neighborhood hη (hc i) (hd i) (hp i) (hdet i) hz t hscale

lemma familyVelocity_zero {a b : ι → Space} {c d : ι → ℝ → Space} {η t : ℝ}
    (hc : ∀ i, deriv (c i) t = 0) (hd : ∀ i j, deriv (fun s => d i s j) t = 0) :
    familyVelocity a b c d η t = 0 := by
  ext x j
  simp [familyVelocity, movingBoxVelocity_zero (hc _) (hd _)]

end BalancedTransport.Geometry
end

end OAI
