import OAI.Geometry.SurfaceImmersion.Whitney.NormalLinearizationHomotopy

namespace OAI

/-! A common vertical column and matching transverse signs preserve rank
under convex interpolation of the endpoint jets. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def triangularPlaneJet (a b c : ℝ) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj 0).smulRight (![a,b] : Base)+
    (ContinuousLinearMap.proj 1).smulRight (![c,0] : Base)

lemma triangularPlaneJet_bijective {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) :
    Function.Bijective (triangularPlaneJet a b c) := by
  have hi : Function.Injective (triangularPlaneJet a b c) := by
    intro u v he
    have h1 : u 0 = v 0 := by
      have hh := congrFun he 1
      simp [triangularPlaneJet] at hh
      exact hh.resolve_right hb
    have h0 := congrFun he 0
    simp only [triangularPlaneJet,add_apply,ContinuousLinearMap.smulRight_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply,
      Matrix.cons_val_zero] at h0
    rw [h1] at h0
    have h2 : u 1 = v 1 := mul_right_cancel₀ hc (add_left_cancel h0)
    ext i
    fin_cases i
    · exact h1
    · exact h2
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (triangularPlaneJet a b c).toLinearMap) rfl).mp hi⟩

lemma plane_jet_bijective_of_columns (L : Base →L[ℝ] Base) {c : ℝ}
    (hc : c ≠ 0) (he : L (![0,1] : Base) = ![c,0])
    (hb : (L (![1,0] : Base)) 1 ≠ 0) : Function.Bijective L := by
  have hL : L = triangularPlaneJet (L ![1,0] 0) (L ![1,0] 1) c := by
    rw [plane_map_columns L,he]
    ext v i
    fin_cases i <;> simp [triangularPlaneJet]
  rw [hL]
  exact triangularPlaneJet_bijective hb hc

lemma convex_same_sign_ne_zero {a b s : ℝ} (hab : 0 < a*b) (hs : s ∈ Icc (0:ℝ) 1) :
    (1-s)*a+s*b ≠ 0 := by
  rcases mul_pos_iff.mp hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hpos : 0 < (1-s)*a+s*b := by
      rcases lt_or_eq_of_le hs.2 with hlt | rfl
      · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) ha) (mul_nonneg hs.1 hb.le)
      · simpa using hb
    exact hpos.ne'
  · have hneg : (1-s)*a+s*b < 0 := by
      rcases lt_or_eq_of_le hs.2 with hlt | rfl
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (by linarith) ha)
          (mul_nonpos_of_nonneg_of_nonpos hs.1 hb.le)
      · simpa using hb
    exact hneg.ne

lemma convex_plane_jets_bijective (L J : Base →L[ℝ] Base) {c s : ℝ}
    (hc : c ≠ 0) (hL : L (![0,1] : Base) = ![c,0])
    (hJ : J (![0,1] : Base) = ![c,0])
    (hprod : 0 < (L (![1,0] : Base) 1)*(J (![1,0] : Base) 1))
    (hs : s ∈ Icc (0:ℝ) 1) : Function.Bijective ((1-s) • L+s • J) := by
  apply plane_jet_bijective_of_columns _ hc
  · simp only [add_apply,smul_apply,hL,hJ]
    rw [←add_smul]
    simp
  · change (1-s)*(L (![1,0] : Base) 1)+s*(J (![1,0] : Base) 1) ≠ 0
    exact convex_same_sign_ne_zero hprod hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
