import OAI.Analysis.StrictMeans.GridChains

namespace OAI

section
open Polynomial Set
namespace StrictInverseFirstPower.Grid
noncomputable section

def coeff (p : Chain) (i j : ℕ) : ℚ := (p.coeff j).coeff i

@[simp] lemma coeff_sub (p q : Chain) (i j : ℕ) :
    coeff (p-q) i j = coeff p i j - coeff q i j := by simp [coeff]

@[simp] lemma coeff_x_zero (p : Chain) (j : ℕ) : coeff (x*p) 0 j = 0 := by
  simp [coeff,x,coeff_C_mul]
@[simp] lemma coeff_x_succ (p : Chain) (i j : ℕ) : coeff (x*p) (i+1) j = coeff p i j := by
  simp [coeff,x,coeff_C_mul,coeff_X_mul]
@[simp] lemma coeff_y_zero (p : Chain) (i : ℕ) : coeff (y*p) i 0 = 0 := by
  simp [coeff,y]
@[simp] lemma coeff_y_succ (p : Chain) (i j : ℕ) : coeff (y*p) i (j+1) = coeff p i j := by
  simp [coeff,y,coeff_X_mul]

lemma finite_coeff_support (p : Chain) : {v : ℕ × ℕ | coeff p v.1 v.2 ≠ 0}.Finite := by
  classical
  apply ((p.support.biUnion fun j => ((p.coeff j).support).map ⟨fun i => (i,j),by intro i k h; exact congrArg Prod.fst h⟩).finite_toSet).subset
  intro v hv
  simp only [Finset.mem_coe,Finset.mem_biUnion,Finset.mem_map]
  refine ⟨v.2,mem_support_iff.mpr ?_,v.1,mem_support_iff.mpr hv,rfl⟩
  intro he
  exact hv (by simp [coeff,he])

structure BoundarySupported (S : Set (ℕ × ℕ)) (a b : Chain) : Prop where
  horizontal : ∀ i j, (i,j) ∉ S ∨ (i+1,j) ∉ S → coeff (faceH a b) i j = 0
  vertical : ∀ i j, (i,j) ∉ S ∨ (i,j+1) ∉ S → coeff (faceV a b) i j = 0
  diagonal : ∀ i j, (i,j) ∉ S ∨ (i+1,j+1) ∉ S → coeff (faceD a b) i j = 0

lemma BoundarySupported.anchor_eq {S : Set (ℕ × ℕ)} {a b : Chain} (hb : BoundarySupported S a b)
    {i j : ℕ} (hv : (i,j) ∉ S) : coeff a i j = coeff b i j := by
  have h := hb.diagonal i j (Or.inl hv)
  exact (sub_eq_zero.mp (by simpa only [faceD,coeff_sub] using h)).symm

lemma BoundarySupported.anchor_zero_axis₁ {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {j : ℕ} (hv : (0,j) ∉ S) : coeff a 0 j = 0 := by
  have h := hb.vertical 0 j (Or.inl hv)
  rw [hb.anchor_eq hv]
  simpa only [faceV,coeff_sub,coeff_x_zero,zero_sub,neg_eq_zero] using h

lemma BoundarySupported.anchor_zero_axis₂ {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i : ℕ} (hv : (i,0) ∉ S) : coeff a i 0 = 0 := by
  have h := hb.horizontal i 0 (Or.inl hv)
  simpa only [faceH,coeff_sub,coeff_y_zero,sub_zero] using h

lemma BoundarySupported.anchor_eq_right {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i+1,j) ∉ S) :
    coeff a i j = coeff a (i+1) j := by
  have h := hb.vertical (i+1) j (Or.inl hv)
  simpa only [faceV,coeff_sub,coeff_x_succ,sub_eq_zero,← hb.anchor_eq hv] using h

lemma BoundarySupported.anchor_eq_up {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i,j) ∉ S) (hw : (i,j+1) ∉ S) :
    coeff a i j = coeff a i (j+1) := by
  have h := hb.horizontal i (j+1) (Or.inl hw)
  exact (sub_eq_zero.mp (by simpa only [faceH,coeff_sub,coeff_y_succ,← hb.anchor_eq hv] using h)).symm

lemma BoundarySupported.anchor_eq_left {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i,j) ∉ S) (hi : 0 < i) :
    coeff a i j = coeff a (i-1) j := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using (hb.anchor_eq_right hv).symm

lemma BoundarySupported.anchor_eq_down {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i,j) ∉ S)
    (hw : (i,j-1) ∉ S) (hj : 0 < j) : coeff a i j = coeff a i (j-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hj)
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using (hb.anchor_eq_up hw hv).symm

lemma BoundarySupported.anchor_zero_of_ascent {u : ℕ × ℕ → ℝ} {c : ℝ} {a b : Chain}
    (hb : BoundarySupported {v | u v ≤ c} a b)
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    ∀ i j, c < u (i,j) → coeff a i j = 0 := by
  classical
  let T : Set (ℕ × ℕ) := {v : ℕ × ℕ | coeff a v.1 v.2 ≠ 0 ∧ c < u v}
  have hT : T.Finite := (finite_coeff_support a).subset (fun _ h => h.1)
  by_contra hall
  push Not at hall
  obtain ⟨i,j,hij,hne⟩ := hall
  have hneT : T.Nonempty := ⟨(i,j),hne,hij⟩
  obtain ⟨v,hv,hmax⟩ := Set.exists_max_image T u hT hneT
  have hvout : v ∉ {w | u w ≤ c} := not_le.mpr hv.2
  have hi : 0 < v.1 := by
    by_contra h
    have hz : v.1 = 0 := Nat.eq_zero_of_not_pos h
    exact hv.1 (by simpa [hz] using hb.anchor_zero_axis₁ (by simpa only [← hz,Prod.mk.eta] using hvout))
  have hj : 0 < v.2 := by
    by_contra h
    have hz : v.2 = 0 := Nat.eq_zero_of_not_pos h
    exact hv.1 (by simpa [hz] using hb.anchor_zero_axis₂ (by simpa only [← hz,Prod.mk.eta] using hvout))
  have hcontr (w : ℕ × ℕ) (hle : u v < u w) (he : coeff a v.1 v.2 = coeff a w.1 w.2) : False := by
    have hw : w ∈ T := ⟨fun h => hv.1 (he.trans h),hv.2.trans hle⟩
    exact (not_lt_of_ge (hmax w hw)) hle
  rcases hascent v.1 v.2 hv.2 hi hj with h|h|h|h
  · exact hcontr (v.1+1,v.2) h (hb.anchor_eq_right (not_le.mpr (hv.2.trans h)))
  · exact hcontr (v.1,v.2+1) h (hb.anchor_eq_up hvout (not_le.mpr (hv.2.trans h)))
  · exact hcontr (v.1-1,v.2) h (hb.anchor_eq_left hvout hi)
  · exact hcontr (v.1,v.2-1) h (hb.anchor_eq_down hvout (not_le.mpr (hv.2.trans h)) hj)

structure FaceSupported (S : Set (ℕ × ℕ)) (a b : Chain) : Prop where
  lower : ∀ i j, coeff a i j ≠ 0 → (i,j) ∈ S ∧ (i+1,j) ∈ S ∧ (i+1,j+1) ∈ S
  upper : ∀ i j, coeff b i j ≠ 0 → (i,j) ∈ S ∧ (i,j+1) ∈ S ∧ (i+1,j+1) ∈ S

lemma BoundarySupported.faceSupported {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) (ha : ∀ i j, (i,j) ∉ S → coeff a i j = 0) : FaceSupported S a b := by
  have hbzero (i j : ℕ) (hv : (i,j) ∉ S) : coeff b i j = 0 :=
    (hb.anchor_eq hv).symm.trans (ha i j hv)
  have hdiag (i j : ℕ) (hv : (i+1,j+1) ∉ S) : coeff b i j = 0 := by
    have hvv := hb.vertical (i+1) (j+1) (Or.inl hv)
    have hhh := hb.horizontal i (j+1) (Or.inr hv)
    simp only [faceV,coeff_sub,coeff_x_succ,hbzero _ _ hv,sub_zero] at hvv
    simpa only [faceH,coeff_sub,coeff_y_succ,hvv,zero_sub,neg_eq_zero] using hhh
  constructor
  · intro i j hne
    refine ⟨?_,?_,?_⟩
    · by_contra hv
      exact hne (ha i j hv)
    · by_contra hv
      exact hne ((hb.anchor_eq_right hv).trans (ha (i+1) j hv))
    · by_contra hv
      have h := hb.diagonal i j (Or.inr hv)
      exact hne (by simpa only [faceD,coeff_sub,hdiag i j hv,zero_sub,neg_eq_zero] using h)
  · intro i j hne
    refine ⟨?_,?_,?_⟩
    · by_contra hv
      exact hne (hbzero i j hv)
    · by_contra hv
      have h := hb.horizontal i (j+1) (Or.inl hv)
      exact hne (by simpa only [faceH,coeff_sub,coeff_y_succ,ha _ _ hv,zero_sub,neg_eq_zero] using h)
    · by_contra hv
      exact hne (hdiag i j hv)

lemma cycle_fills_sublevel {u : ℕ × ℕ → ℝ} {c : ℝ} {h v d : Chain}
    (hc : boundary₁ h v d = 0)
    (hH : ∀ i j, c < u (i,j) ∨ c < u (i+1,j) → coeff h i j = 0)
    (hV : ∀ i j, c < u (i,j) ∨ c < u (i,j+1) → coeff v i j = 0)
    (hD : ∀ i j, c < u (i,j) ∨ c < u (i+1,j+1) → coeff d i j = 0)
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    ∃ a b, faceH a b = h ∧ faceV a b = v ∧ faceD a b = d ∧
      FaceSupported {w | u w ≤ c} a b := by
  obtain ⟨a,b,ha,hb,hd⟩ := cycle_fills hc
  have hs : BoundarySupported {w | u w ≤ c} a b := by
    constructor
    · simpa only [ha,mem_ofPred_eq,not_le] using hH
    · simpa only [hb,mem_ofPred_eq,not_le] using hV
    · simpa only [hd,mem_ofPred_eq,not_le] using hD
  refine ⟨a,b,ha,hb,hd,hs.faceSupported ?_⟩
  intro i j hi
  exact hs.anchor_zero_of_ascent hascent i j (not_le.mp hi)

end
end StrictInverseFirstPower.Grid

end

end OAI
