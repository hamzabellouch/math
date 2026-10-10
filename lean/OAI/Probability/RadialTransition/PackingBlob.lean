import OAI.Probability.RadialTransition.TetraGeometry

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

def packingBlob (ν b : ℝ) (z : Position) : Set Position := translateSet ((1+ν) • z) (cube b)

lemma packingBlob_distance {ν b : ℝ} {z x : Position} (hb : 0 ≤ b)
    (hx : x ∈ packingBlob ν b z) : dist x ((1+ν) • z) ≤ 2*b := by
  apply dist_le_twice_coordinate hb
  intro k
  have hk := hx k
  change 0 ≤ x k-(1+ν)*z k ∧ x k-(1+ν)*z k ≤ b at hk
  change |x k-(1+ν)*z k| ≤ b
  rw [abs_of_nonneg hk.1]
  exact hk.2

lemma packingBlob_separation {ν b : ℝ} {z w x y : Position} (hν : 0 ≤ ν) (hb : 0 ≤ b)
    (hzw : 1 ≤ dist z w) (hx : x ∈ packingBlob ν b z) (hy : y ∈ packingBlob ν b w) :
    1+ν-4*b ≤ dist x y := by
  have hz := packingBlob_distance hb hx
  have hw := packingBlob_distance hb hy
  have hd : dist ((1+ν) • z) ((1+ν) • w) = (1+ν)*dist z w := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), dist_eq_norm]
  have he := dist_triangle4 ((1+ν) • z) x y ((1+ν) • w)
  rw [hd, dist_comm ((1+ν) • z) x] at he
  have hm := mul_le_mul_of_nonneg_left hzw (show 0 ≤ 1+ν by linarith)
  linarith

lemma packingBlob_subset_cube {L ν b : ℝ} (hν : 0 ≤ ν) {z : Position} (hz : z ∈ cube L) :
    packingBlob ν b z ⊆ cube ((1+ν)*L+b) := by
  intro x hx k
  have hk := hx k
  change 0 ≤ x k-(1+ν)*z k ∧ x k-(1+ν)*z k ≤ b at hk
  have hzk := hz k
  have hl : 0 ≤ (1+ν)*z k := mul_nonneg (by linarith) hzk.1
  have hu := mul_le_mul_of_nonneg_left hzk.2 (show 0 ≤ 1+ν by linarith)
  constructor <;> linarith

lemma core_grand_packing_lower {L ν b t β h : ℝ} (ht : 0 < t) (hb : 0 ≤ b)
    (hν : 0 ≤ ν) (hsep : 1/t+4*b ≤ ν) (hβ : 0 ≤ β) :
    grandOn (corePotential t) (cube b) β (t*h) ^ packingNumber L ≤
      grandOn (corePotential t) (cube ((1+ν)*L+b)) β (t*h) := by
  classical
  obtain ⟨X, hcard, hX⟩ := packingNumber_attained L
  let φ := corePotential t
  have hc := continuous_corePotential t
  have hbound := bounded_corePotential t
  have hstable := stable_corePotential t
  have hA (z : Position) : MeasurableSet (packingBlob ν b z) := measurableSet_translate (measurableSet_cube _)
  have hAfin (z : Position) : volume (packingBlob ν b z) ≠ ⊤ := by
    rw [packingBlob, volume_translateSet _ _ (measurableSet_cube _), volume_cube]
    finiteness
  have hdist (z : Position) (hz : z ∈ X) (w : Position) (hw : w ∈ X) (hne : z ≠ w)
      (x : Position) (hx : x ∈ packingBlob ν b z) (y : Position) (hy : y ∈ packingBlob ν b w) :
      1+1/t ≤ dist x y := by
    have hh := packingBlob_separation hν hb (hX.2 z hz w hw hne) hx hy
    linarith
  have hdisj : ∀ z ∈ X, ∀ w ∈ X, z ≠ w → Disjoint (packingBlob ν b z) (packingBlob ν b w) := by
    intro z hz w hw hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hh := hdist z hz w hw hne x hx x hy
    rw [dist_self] at hh
    have := one_div_pos.mpr ht
    linarith
  have hcross : ∀ z ∈ X, ∀ w ∈ X, z ≠ w → ∀ x ∈ packingBlob ν b z,
      ∀ y ∈ packingBlob ν b w, φ (nndist x y) ≤ 0 := by
    intro z hz w hw hne x hx y hy
    exact le_of_eq (coreReal_zero_outer ht (hdist z hz w hw hne x hx y hy))
  have hprod := grandOn_biUnion_lower hc hbound hstable hβ X (packingBlob ν b) (t*h)
    (fun z _ => hA z) (fun z _ => hAfin z) hdisj hcross
  have hsub : (⋃ z ∈ X, packingBlob ν b z) ⊆ cube ((1+ν)*L+b) := by
    intro x hx
    obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp hx
    exact packingBlob_subset_cube hν (hX.1 z hz) hxz
  have hcomp := grandOn_mono hc hbound hstable hβ hsub (by rw [volume_cube]; finiteness) (t*h)
  simp only [packingBlob, grandOn_translate, Finset.prod_const, hcard] at hprod
  exact hprod.trans hcomp

end RadialTransition
end

end OAI
