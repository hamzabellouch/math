import OAI.Combinatorics.ThinTrees.Partitions

namespace OAI

universe uV uU uI

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset
variable {h : ℕ}

def antipode (x : Fin h → ℝ) : Fin h → ℝ := fun j => 1-x j

lemma binary_antipode {x : Fin h → ℝ} (hx : binary x) : binary (antipode x) := by
  intro j
  rcases hx j with hh | hh <;> simp [antipode,hh]

lemma radial_complement {x z : Fin h → ℝ} (hx : binary x) (hz : cube z) :
    l1dist z x+l1dist z (antipode x) = h := by
  rw [l1dist,l1dist,← sum_add_distrib]
  calc
    _ = ∑j : Fin h, (1:ℝ) := by
      apply sum_congr rfl
      intro j hj
      rcases hx j with hh | hh
      · simp only [hh,antipode,sub_zero,abs_of_nonneg (hz j).1,
          abs_of_nonpos (by linarith [(hz j).2] : z j-1 ≤ 0)]
        ring
      · simp only [hh,antipode,sub_self,sub_zero,abs_of_nonneg (hz j).1,
          abs_of_nonpos (by linarith [(hz j).2] : z j-1 ≤ 0)]
        ring
    _ = h := by simp

lemma radial_max {x z : Fin h → ℝ} (hx : binary x) (hz : cube z) :
    l1dist z x ≤ h := by
  have hh := radial_complement hx hz
  linarith [l1dist_nonneg z (antipode x)]

lemma binary_radial_move {x z : Fin h → ℝ} (hx : binary x) (hz : binary z)
    {r : ℝ} (hr : 0 ≤ r) (hrmax : r ≤ h) :
    ∃w : Fin h → ℝ, cube w ∧ l1dist w x = r ∧ l1dist w z = |r-l1dist z x| := by
  let R := l1dist z x
  by_cases heq : r = R
  · exact ⟨z,binary_cube hz,heq.symm,by rw [heq]; simp [R,l1dist_self]⟩
  rcases lt_or_gt_of_ne heq with hlo | hhi
  · have hR : 0 < R := lt_of_le_of_lt hr hlo
    let t := (R-r)/R
    have ht : t ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (by linarith) hR.le,(div_le_one hR).mpr (by linarith)⟩
    have hmul : t*R = R-r := div_mul_cancel₀ _ hR.ne'
    let w := fun j => z j+t*(x j-z j)
    refine ⟨w,cube_segment (binary_cube hz) (binary_cube hx) ht,?_,?_⟩
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hx) hx ht
      rw [l1dist_self] at hh
      dsimp [w]
      rw [hh]
      dsimp [R] at hmul
      nlinarith
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hx) hz ht
      rw [l1dist_self,l1dist_comm x z] at hh
      dsimp [w]
      rw [hh,abs_of_neg (by linarith : r-l1dist z x < 0)]
      dsimp [R] at hmul
      nlinarith
  · let y := antipode x
    have hy := binary_antipode hx
    have hcomp : R+l1dist y z = h := by
      simpa only [R,l1dist_comm y z] using radial_complement hx (binary_cube hz)
    have hyx : l1dist y x = h := by
      have hh := radial_complement hx (binary_cube hy)
      simpa only [y,l1dist_self,add_zero] using hh
    let D := l1dist y z
    have hD : 0 < D := by dsimp [D]; linarith
    let t := (r-R)/D
    have ht : t ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (by linarith) hD.le,(div_le_one hD).mpr (by dsimp [D]; linarith)⟩
    have hmul : t*D = r-R := div_mul_cancel₀ _ hD.ne'
    let w := fun j => z j+t*(y j-z j)
    refine ⟨w,cube_segment (binary_cube hz) (binary_cube hy) ht,?_,?_⟩
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hy) hx ht
      rw [hyx] at hh
      dsimp [w]
      rw [hh]
      dsimp [R,D] at hmul hcomp
      nlinarith
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hy) hz ht
      rw [l1dist_self] at hh
      dsimp [w]
      rw [hh,abs_of_pos (by exact sub_pos.mpr hhi)]
      dsimp [R,D] at hmul
      nlinarith

namespace RadialShell
variable {V : Type uV} {X : V → Fin h → ℝ}

lemma ball_meets_radial {B : RadialShell V} (hX : ∀v, binary (X v))
    (hB : B.Valid X) (z : V) {δ : ℝ} (hδ : 0 < δ)
    (hlo : B.inner-δ < l1dist (X z) (X B.center))
    (hhi : l1dist (X z) (X B.center) < B.outer+δ) :
    ¬Disjoint ((ball z δ).support X) (B.support X) := by
  have hinterval : max B.inner (l1dist (X z) (X B.center)-δ) <
      min B.outer (l1dist (X z) (X B.center)+δ) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    exact ⟨⟨hB.2.1,by linarith⟩,⟨by linarith,by linarith⟩⟩
  obtain ⟨r,hl,hr⟩ := exists_between hinterval
  have hlo' : B.inner < r := (le_max_left _ _).trans_lt hl
  have hhi' : r < B.outer := hr.trans_le (min_le_left _ _)
  have hradlo : l1dist (X z) (X B.center)-δ < r := (le_max_right _ _).trans_lt hl
  have hradhi : r < l1dist (X z) (X B.center)+δ := hr.trans_le (min_le_right _ _)
  obtain ⟨v,hv⟩ := hB.2.2.2.2
  have hmax : B.outer ≤ h := hv.trans (radial_max (hX _) (binary_cube (hX v)))
  obtain ⟨w,hw,hwr,hwz⟩ := binary_radial_move (hX B.center) (hX z)
    (hB.1.trans hlo'.le) (hhi'.le.trans hmax)
  have hwA : w ∈ (ball z δ).support X := by
    rw [support_ball]
    refine ⟨hw,?_⟩
    rw [hwz,abs_lt]
    constructor <;> linarith
  have hwB : w ∈ B.support X := ⟨hw,hwr ▸ hhi',Or.inr (hwr ▸ hlo')⟩
  exact fun hdis => Set.disjoint_left.mp hdis hwA hwB

end RadialShell
end
end StrongThinTree.Geometry

namespace StrongThinTree.AssignedAccounting
noncomputable section

def base (avoiding : Bool) (R δ : ℝ) : ℝ :=
  max (R-3*δ) 0 / (if avoiding then 10 else 1)

def fresh (δ ε : ℝ) : ℝ := δ-3*ε

def theta : ℝ := 1/512

lemma base_le_width (a : Bool) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) :
    base a R δ ≤ R := by
  have hh : max (R-3*δ) 0 ≤ R := max_le (by linarith) hR
  cases a <;> simp only [base,Bool.false_eq_true,↓reduceIte,div_one] <;> linarith

lemma base_discard (a : Bool) {R δ : ℝ} (hR : R ≤ 0) (hδ : 0 ≤ δ) :
    base a R δ = 0 := by
  have : max (R-3*δ) 0 = 0 := max_eq_right (by linarith)
  simp [base,this]

lemma fresh_lower {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) :
    (5/6:ℝ)*δ ≤ fresh δ ε := by dsimp [fresh]; linarith

lemma avoiding_carve {δ ε R R₁ R₂ : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-2*δ) :
    base true R δ + theta*δ ≤ base true R₁ δ+base true R₂ δ+fresh δ ε := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have hf := fresh_lower hδ hε
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,↓reduceIte,hr,theta]
  linarith

lemma dense_carve {δ ε R R₁ R₂ L M : ℝ}
    (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) (hM : 0 ≤ M)
    (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-L-4*δ)
    (hdense : 3*L ≤ M*δ) (hcount : 765*δ ≤ M*δ) :
    base false R δ+theta*M*δ ≤
      base false R₁ δ+base false R₂ δ+M*fresh δ ε := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have hf := mul_le_mul_of_nonneg_left (fresh_lower hδ hε) hM
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,Bool.false_eq_true,↓reduceIte,div_one,hr,theta]
  nlinarith

lemma sparse_carve {δ R R₁ R₂ L M : ℝ}
    (hδ : 0 ≤ δ) (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-L)
    (hwidth : 255*δ ≤ L) (hsparse : M*δ ≤ 3*L) :
    base false R δ+theta*M*δ ≤
      base false R₁ δ+base false R₂ δ+base false (L-2*δ) δ+base true L δ := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have h3 := le_max_left (L-2*δ-3*δ) 0
  have h4 := le_max_left (L-3*δ) 0
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,Bool.false_eq_true,↓reduceIte,div_one,hr,theta]
  linarith

lemma shrink_cost (a : Bool) {R δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536) :
    0 ≤ base a R δ-base a (R-514*δ) ε ∧
    base a R δ-base a (R-514*δ) ε ≤
      256*(base a R ε-base a R δ) := by
  have hthreshold : R-514*δ-3*ε ≤ R-3*δ := by linarith
  have hmono := max_le_max_right (0:ℝ) hthreshold
  have hr : max (R-3*δ) 0-max (R-514*δ-3*ε) 0 ≤
      256*(max (R-3*ε) 0-max (R-3*δ) 0) := by
    by_cases hh : R ≤ 3*δ
    · rw [max_eq_right (by linarith : R-3*δ ≤ 0)]
      have h0 := le_max_right (R-514*δ-3*ε) 0
      have h1 := le_max_right (R-3*ε) 0
      linarith
    · have hd : 3*δ ≤ R := (not_le.mp hh).le
      rw [max_eq_left (by linarith : 0 ≤ R-3*δ),
        max_eq_left (by linarith : 0 ≤ R-3*ε)]
      have hlo := le_max_left (R-514*δ-3*ε) 0
      linarith
  cases a <;> simp only [base,Bool.false_eq_true,↓reduceIte,div_one] <;>
    constructor <;> linarith

lemma border_payment {δ ε B D : ℝ}
    (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) (hB : 0 ≤ B)
    (hD : D ≤ B*δ/2) : theta*B*δ+D ≤ B*fresh δ ε := by
  have hh := mul_le_mul_of_nonneg_left (fresh_lower hδ hε) hB
  have hnon : 0 ≤ B*δ := mul_nonneg hB hδ
  dsimp [theta]
  nlinarith

end
end StrongThinTree.AssignedAccounting

namespace StrongThinTree.AssignedSelection
noncomputable section
open Finset

lemma large_neighbor_class {U : Type uU} {I : Type uI} [DecidableEq U] [DecidableEq I]
    (A : Finset U) (P : Finset I) (R : U → I → Prop) [DecidableRel R]
    (hP : P.Nonempty) (hcover : ∀u ∈ A, ∃i ∈ P, R u i)
    {q O : ℝ} (hq : 0 < q) (hO : 0 < O)
    (hparts : q*(P.card : ℝ) ≤ 2*O) (hmany : 1536*O ≤ q*(A.card : ℝ)) :
    ∃i ∈ P, 768 ≤ (A.filter (fun u => R u i)).card := by
  obtain ⟨i,hi,hmax⟩ := P.exists_max_image (fun i => (A.filter (fun u => R u i)).card) hP
  have hcover' : A = P.biUnion (fun i => A.filter (fun u => R u i)) := by
    ext u
    simp only [mem_biUnion,mem_filter]
    constructor
    · intro hu
      obtain ⟨j,hj,hr⟩ := hcover u hu
      exact ⟨j,hj,hu,hr⟩
    · rintro ⟨j,hj,hu,hr⟩
      exact hu
  have hc : A.card ≤ P.card*(A.filter (fun u => R u i)).card := by
    calc
      A.card = (P.biUnion (fun i => A.filter (fun u => R u i))).card := congrArg card hcover'
      _ ≤ ∑j ∈ P, (A.filter (fun u => R u j)).card := card_biUnion_le
      _ ≤ ∑j ∈ P, (A.filter (fun u => R u i)).card := sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp
  have hc' : (A.card : ℝ) ≤ (P.card : ℝ)*(A.filter (fun u => R u i)).card := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hc' hq.le
  have hp := mul_le_mul_of_nonneg_right hparts
    (Nat.cast_nonneg (A.filter (fun u => R u i)).card : (0:ℝ) ≤ _)
  have hn : (768:ℝ) ≤ (A.filter (fun u => R u i)).card := by nlinarith
  exact ⟨i,hi,by exact_mod_cast hn⟩

lemma radial_range {r₁ r₂ p q s₀ u₀ s u δ : ℝ}
    (hδ : 0 < δ) (hp0 : p ≤ s₀) (hq0 : s₀ ≤ q)
    (hu₀lo : r₁+256*δ < u₀) (hu₀hi : u₀ < r₂-256*δ)
    (hnear0 : |u₀-s₀| < δ) (hp : p ≤ s) (hq : s ≤ q)
    (hnear : |u-s| < δ)
    (hout : ¬(max r₁ p-δ < u ∧ u < min r₂ q+δ)) :
    255*δ ≤ min r₂ q-max r₁ p := by
  obtain ⟨hn0a,hn0b⟩ := abs_lt.mp hnear0
  obtain ⟨hna,hnb⟩ := abs_lt.mp hnear
  have hslo : r₁+255*δ < s₀ := by linarith
  have hshi : s₀ < r₂-255*δ := by linarith
  have ha : max r₁ p ≤ s₀ := max_le (by linarith) hp0
  have hb : s₀ ≤ min r₂ q := le_min (by linarith) hq0
  by_cases hul : max r₁ p-δ < u
  · have huh : min r₂ q+δ ≤ u := le_of_not_gt (fun hh => hout ⟨hul,hh⟩)
    have hclip : r₂ ≤ q := by
      by_contra hh
      rw [min_eq_right (not_le.mp hh).le] at huh
      linarith
    rw [min_eq_left hclip]
    linarith
  · have hul : u ≤ max r₁ p-δ := not_lt.mp hul
    have hclip : p ≤ r₁ := by
      by_contra hh
      rw [max_eq_right (not_le.mp hh).le] at hul
      linarith
    rw [max_eq_left hclip]
    linarith

lemma interior_neighbor_in_range {r₁ r₂ p q s u δ : ℝ}
    (hδ : 0 < δ) (hp : p ≤ s) (hq : s ≤ q)
    (hulo : r₁+256*δ < u) (huhi : u < r₂-256*δ)
    (hnear : |u-s| < δ) :
    max r₁ p ≤ min r₂ q ∧ max r₁ p-δ < u ∧ u < min r₂ q+δ := by
  obtain ⟨hna,hnb⟩ := abs_lt.mp hnear
  have ha : max r₁ p ≤ s := max_le (by linarith) hp
  have hb : s ≤ min r₂ q := le_min (by linarith) hq
  exact ⟨ha.trans hb,by linarith,by linarith⟩

lemma dense_count {δ L M N : ℝ} (hδ : 0 ≤ δ) (hN : 768 ≤ N)
    (hdich : N ≤ M ∨ 255*δ ≤ L) (hdense : 3*L ≤ M*δ) : 765*δ ≤ M*δ := by
  rcases hdich with hh | hh
  · have := mul_le_mul_of_nonneg_right hh hδ
    nlinarith
  · linarith

lemma sparse_width {δ L M N : ℝ} (hδ : 0 ≤ δ) (hN : 768 ≤ N)
    (hdich : N ≤ M ∨ 255*δ ≤ L) (hsparse : M*δ ≤ 3*L) : 255*δ ≤ L := by
  rcases hdich with hh | hh
  · have := mul_le_mul_of_nonneg_right hh hδ
    nlinarith
  · exact hh

end
end StrongThinTree.AssignedSelection

end

end OAI
