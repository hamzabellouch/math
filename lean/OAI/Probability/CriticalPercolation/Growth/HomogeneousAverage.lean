import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteActionAverage
import OAI.Probability.CriticalPercolation.Growth.HomogeneousTransport

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open ActionOrbitTransport

variable {X : Type*} (W : Geometry X)

abbrev Stab := MulAction.stabilizer W.Aut W.root

def frame (x : X) : W.Aut := (W.transitive W.root x).choose
lemma frame_root (x : X) : W.frame x W.root=x := (W.transitive W.root x).choose_spec
lemma frame_smul_root (x : X) : W.frame x • W.root=x := W.frame_root x
lemma action_transitive : ∀ x y : X, ∃ g : W.Aut, g • x=y := W.transitive

lemma suborbit_finite (x y : X) : (stabilizerOrbit W.Aut X x y).Finite := by
  obtain ⟨p,_,_⟩ := W.connected.exists_path_of_dist x y
  apply (W.around x p.length).finite_toSet.subset
  intro z hz
  obtain ⟨g,hgx,rfl⟩ := (mem_stabilizerOrbit W.Aut X).mp hz
  change g x=x at hgx
  change g y∈W.around x p.length
  apply W.mem_around.mpr
  simpa only [hgx] using GraphTopology.iso_reachBall W.graph g (show y∈GraphTopology.reachBall W.graph x p.length from ⟨p,le_rfl⟩)

lemma suborbit_card_pos (x y : X) : 0<suborbitCard W.Aut X x y := by
  apply Set.ncard_pos (W.suborbit_finite x y) |>.mpr
  exact ⟨y,(mem_stabilizerOrbit W.Aut X).mpr ⟨1,one_smul _ _,one_smul _ _⟩⟩

lemma stab_ball_preserved (N : ℕ) (k : W.Stab) (x : X) (hx : x∈W.ball N) : k • x∈W.ball N := by
  have hk : k.val W.root=W.root := k.property
  change k.val x∈W.around W.root N
  rw [←hk,←W.aut_around_image]
  exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

lemma row_image (b x : X) :
    (W.suborbit_finite W.root b).toFinset.image (W.frame x)=
      (pair_row_finite W.action_transitive W.suborbit_finite W.root b x).toFinset := by
  ext y
  simp only [Finset.mem_image,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨k,hk,hz⟩ := (mem_stabilizerOrbit W.Aut X).mp hz
    apply (pairOrbit_eq W.Aut X).mpr
    refine ⟨(W.frame x*k)⁻¹,?_,?_⟩
    · have he : (W.frame x*k) • W.root=x := by
        rw [mul_smul,hk]; exact W.frame_root x
      calc
        _ = (W.frame x*k)⁻¹ • ((W.frame x*k) • W.root) := congrArg _ he.symm
        _ = _ := inv_smul_smul _ _
    · have he : (W.frame x*k) • b=W.frame x z := by rw [mul_smul,hz]; rfl
      rw [←he,inv_smul_smul]
  · intro hy
    obtain ⟨g,hx,hb⟩ := (pairOrbit_eq W.Aut X).mp hy
    refine ⟨(W.frame x)⁻¹ • y,?_,smul_inv_smul (W.frame x) y⟩
    apply (mem_stabilizerOrbit W.Aut X).mpr
    refine ⟨(g*W.frame x)⁻¹,?_,?_⟩
    · have he : (g*W.frame x) • W.root=W.root := by rw [mul_smul,W.frame_smul_root,hx]
      calc
        _ = (g*W.frame x)⁻¹ • ((g*W.frame x) • W.root) := congrArg _ he.symm
        _ = _ := inv_smul_smul _ _
    · rw [mul_inv_rev,mul_smul,←hb,inv_smul_smul]

lemma average_row {H : Type*} [Group H] [Fintype H]
    (N : ℕ) (r : H → W.Stab)
    (hm : ∀ a b x, x∈W.ball N → r (a*b) • x=r a • (r b • x))
    (hs : ∀ k : W.Stab, ∃ h : H, ∀ x∈W.ball N, r h • x=k • x)
    (b : X) (hb : b∈W.ball N) (x : X) (f : X → ℝ) :
    (suborbitCard W.Aut X W.root b : ℝ)*(∑ h : H, f (W.frame x (r h • b)))=
      (Fintype.card H : ℝ)*∑ y∈(pair_row_finite W.action_transitive W.suborbit_finite W.root b x).toFinset, f y := by
  have hh := restricted_orbit_average (G:=W.Stab) (W.ball N : Set X) r hm hs b hb
    (W.suborbit_finite W.root b) (fun z => f (W.frame x z))
  change (suborbitCard W.Aut X W.root b : ℝ)*_= _ at hh
  rw [←W.row_image,Finset.sum_image]
  · exact hh
  · intro a _ b _ he; exact (W.frame x).injective he

lemma average_sum_bound
    (hu : ∀ x y, suborbitCard W.Aut X x y=suborbitCard W.Aut X y x)
    {H : Type*} [Group H] [Fintype H] (N : ℕ) (r : H → W.Stab)
    (hm : ∀ a b x, x∈W.ball N → r (a*b) • x=r a • (r b • x))
    (hs : ∀ k : W.Stab, ∃ h : H, ∀ x∈W.ball N, r h • x=k • x)
    (b : X) (hb : b∈W.ball N) (R : ℕ) (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ x∈W.ball R, ∑ h : H, f (W.frame x (r h • b)))≤
      (Fintype.card H : ℝ)*∑ y∈W.ball (R+N), f y := by
  have hrow := finite_row_sum_bound W.action_transitive W.suborbit_finite hu W.root b
    (W.ball R) (W.ball (R+N)) f (fun y _ => hf y) (by
      intro x hx y hy
      obtain ⟨g,hgx,hgy⟩ := (pairOrbit_eq W.Aut X).mp hy
      change g x=W.root at hgx
      change g y=b at hgy
      have hyx : y∈W.around x N := by
        have hbx : g y∈W.around (g x) N := by rw [hgx,hgy]; exact hb
        rw [←W.aut_around_image] at hbx
        obtain ⟨z,hz,hze⟩ := Finset.mem_image.mp hbx
        exact (g.injective hze) ▸ hz
      exact W.mem_around_add hx hyx)
  have he : (suborbitCard W.Aut X W.root b : ℝ)*
      (∑ x∈W.ball R, ∑ h : H, f (W.frame x (r h • b)))=
      (Fintype.card H : ℝ)*∑ x∈W.ball R,
        ∑ y∈(pair_row_finite W.action_transitive W.suborbit_finite W.root b x).toFinset, f y := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simpa only [Finset.mul_sum] using W.average_row N r hm hs b hb x f
  have hi := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg (Fintype.card H))
  rw [←he] at hi
  have hp : (0:ℝ)<suborbitCard W.Aut X W.root b := by exact_mod_cast W.suborbit_card_pos W.root b
  nlinarith

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
