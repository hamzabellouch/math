import OAI.MathematicalPhysics.Heisenberg.LatticeCuts

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma exists_box {d : ℕ} (x : Site d) : ∃ r : ℕ, x ∈ Box (r : ℤ) := by
  refine ⟨Finset.univ.sup (fun i => (x i).natAbs),?_⟩
  intro j
  rw [← Int.natCast_natAbs]
  exact_mod_cast (Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ j))

lemma exterior_to_shell {d : ℕ} (r R : ℤ) (hr : 0 ≤ r) (hR : r < R)
    (x : Site d) (hx : x ∉ Box r) (hxR : x ∈ Box R) :
    ∃ y ∈ Shell R, Reach (Box r)ᶜ x y := by
  obtain ⟨j,hj⟩ : ∃ j, r < |x j| := by
    simpa only [Box,Set.mem_ofPred_eq,not_forall,not_le] using hx
  let b : ℤ := if 0 ≤ x j then R else -R
  let y := Function.update x j b
  have hb : |b| = R := by
    dsimp [b]
    split_ifs <;> simp [abs_of_nonneg (by omega : 0 ≤ R)]
  have hy : y ∈ Shell R := by
    refine ⟨?_,j,?_⟩
    · intro k
      by_cases hk : k = j
      · subst k; simpa [y] using hb.le
      · simpa [y,hk] using hxR k
    · simpa [y] using hb
  refine ⟨y,hy,?_⟩
  rw [← Function.update_eq_self j x]
  apply reach_axis
  intro t ht₁ ht₂ ht
  have htj : |t| ≤ r := by simpa using ht j
  have hbound := abs_le.mp (hxR j)
  have htbound := abs_le.mp htj
  by_cases h : 0 ≤ x j
  · have hb' : b = R := ite_eq_left h
    rw [hb',min_eq_left hbound.2] at ht₁
    rw [abs_of_nonneg h] at hj
    omega
  · have hb' : b = -R := ite_eq_right h
    rw [hb',max_eq_left hbound.1] at ht₂
    rw [abs_of_neg (by omega)] at hj
    omega

lemma exterior_connected {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (x y : Site d) (hx : x ∉ Box r) (hy : y ∉ Box r) :
    Reach (Box r)ᶜ x y := by
  obtain ⟨a,ha⟩ := exists_box x
  obtain ⟨b,hb⟩ := exists_box y
  let R : ℤ := max (max a b) (r+1)
  have hR : r < R := by have := le_max_right (max (a:ℤ) b) (r+1); dsimp [R]; omega
  have haR : (a:ℤ) ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hbR : (b:ℤ) ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨v,hv,hxv⟩ := exterior_to_shell r R hr hR x hx (box_mono haR ha)
  obtain ⟨w,hw,hyw⟩ := exterior_to_shell r R hr hR y hy (box_mono hbR hb)
  have hvw : Reach (Box r)ᶜ v w := by
    apply reach_mono _ (shell_connected hd R (by omega) v w hv hw)
    intro z hz hzr
    obtain ⟨j,hj⟩ := hz.2
    have := hzr j
    omega
  exact hxv.trans (hvw.trans (reach_symm hyw))

lemma reach_end_mem {d : ℕ} {U : Set (Site d)} {x y : Site d}
    (hx : x ∈ U) (h : Reach U x y) : y ∈ U := by
  induction h with
  | refl => exact hx
  | tail _ h _ => exact h.2.2

lemma ambient_connected {d : ℕ} (x y : Site d) : Reach Set.univ x y :=
  reach_rectangle Set.univ x y (by simp)

end Heisenberg.Geometry

namespace Heisenberg.LatticeHull
open Heisenberg.Geometry

def Hull {d : ℕ} (A : Set (Site d)) (b : Site d) : Set (Site d) :=
  {x | ¬ Reach Aᶜ b x}

lemma subset_hull {d : ℕ} (A : Set (Site d)) {b : Site d} (hb : b ∉ A) : A ⊆ Hull A b := by
  intro x hx hr
  exact reach_end_mem hb hr hx

lemma complement_connected {d : ℕ} (A : Set (Site d)) (b : Site d) :
    Heisenberg.LatticeCut.Connected (Hull A b)ᶜ := by
  intro x hx y hy
  have hx' : Reach Aᶜ b x := not_not.mp hx
  have hy' : Reach Aᶜ b y := not_not.mp hy
  have hr : Reach Aᶜ x y := (reach_symm hx').trans hy'
  induction hr with
  | refl => exact reach_refl _ _
  | @tail z w hz hw ih =>
    have hz' : Reach Aᶜ b z := hx'.trans hz
    exact (ih (not_not.mpr hz') hz').tail ⟨hw.1,not_not.mpr hz',not_not.mpr (hz'.tail hw)⟩

lemma inner_endpoint_mem {d : ℕ} (A : Set (Site d)) {b : Site d} (hb : b ∉ A)
    {x y : Site d} (hx : x ∈ Hull A b) (hy : y ∉ Hull A b) (hxy : Step x y) : x ∈ A := by
  by_contra h
  have hy' : Reach Aᶜ b y := not_not.mp hy
  exact hx (hy'.tail ⟨step_symm hxy,reach_end_mem hb hy',h⟩)

lemma hull_connected {d : ℕ} (A : Set (Site d)) (hA : Heisenberg.LatticeCut.Connected A)
    (hAn : A.Nonempty) {b : Site d} (hb : b ∉ A) :
    Heisenberg.LatticeCut.Connected (Hull A b) := by
  obtain ⟨a,ha⟩ := hAn
  have hAH := subset_hull A hb
  have hAll : ∀ x, x ∉ Hull A b ∨ Reach (Hull A b) a x := by
    intro x
    have hr := ambient_connected a x
    induction hr with
    | refl => exact Or.inr (reach_refl _ _)
    | @tail z w _ hzw ih =>
      by_cases hw : w ∈ Hull A b
      · right
        rcases ih with hz | hz
        · have hwA := inner_endpoint_mem A hb hw hz (step_symm hzw.1)
          exact reach_mono hAH (hA a ha w hwA)
        · exact hz.tail ⟨hzw.1,reach_end_mem (hAH ha) hz,hw⟩
      · exact Or.inl hw
  intro x hx y hy
  exact (reach_symm ((hAll x).resolve_left (fun h => h hx))).trans
    ((hAll y).resolve_left (fun h => h hy))

lemma hull_subset_box {d : ℕ} (hd : 2 ≤ d) (A : Set (Site d)) (r : ℤ) (hr : 0 ≤ r)
    (hAr : A ⊆ Box r) {b : Site d} (hb : b ∉ Box r) : Hull A b ⊆ Box r := by
  intro x hx
  by_contra hxr
  apply hx
  apply reach_mono _ (exterior_connected hd r hr b x hb hxr)
  intro z hz hzA
  exact hz (hAr hzA)

lemma base_independence {d : ℕ} (A : Set (Site d)) {b c : Site d}
    (hbc : Reach Aᶜ b c) : Hull A b = Hull A c := by
  ext x
  constructor
  · intro hx hcx
    exact hx (hbc.trans hcx)
  · intro hx hbx
    exact hx ((reach_symm hbc).trans hbx)

lemma box_finite {d : ℕ} (r : ℕ) : (Box (r : ℤ) : Set (Site d)).Finite := by
  have he : Box (r : ℤ) = (boxFinset d r : Set (Site d)) := by
    ext x; exact (mem_boxFinset ..).symm
  rw [he]
  exact Finset.finite_toSet _

lemma finite_contained_box {d : ℕ} (A : Set (Site d)) (hA : A.Finite) :
    ∃ r : ℕ, A ⊆ Box (r : ℤ) := by
  have hx : ∀ x ∈ A, ∃ r : ℕ, x ∈ Box (r : ℤ) := fun x _ => exists_box x
  choose r hr using hx
  let R := hA.toFinset.sup (fun x => if h : x ∈ A then r x h else 0)
  refine ⟨R,?_⟩
  intro x hx
  apply box_mono _ (hr x hx)
  have hle : r x hx ≤ R := by
    simpa only [dite_eq_left hx] using Finset.le_sup (f := fun x => if h : x ∈ A then r x h else 0)
      (hA.mem_toFinset.mpr hx)
  exact_mod_cast hle

lemma hull_finite {d : ℕ} (hd : 2 ≤ d) (A : Set (Site d)) (r : ℕ)
    (hAr : A ⊆ Box (r : ℤ)) {b : Site d} (hb : b ∉ Box (r : ℤ)) :
    (Hull A b).Finite :=
  (box_finite r).subset (hull_subset_box hd A r (by positivity) hAr hb)

lemma exterior_iff_unbounded {d : ℕ} (hd : 2 ≤ d) (A : Set (Site d)) (r : ℕ)
    (hAr : A ⊆ Box (r : ℤ)) {b x : Site d} (hb : b ∉ Box (r : ℤ)) :
    x ∉ Hull A b ↔ ∀ R : ℕ, ∃ y, Reach Aᶜ x y ∧ y ∉ Box (R : ℤ) := by
  have hbA : b ∉ A := fun h => hb (hAr h)
  constructor
  · intro hx R
    let y : Site d := fun _ => (max r R : ℕ)+1
    have hy : y ∉ Box (max r R : ℕ) := by
      intro h
      have h0 := h ⟨0,by omega⟩
      simp only [y,abs_of_nonneg (by positivity : (0:ℤ) ≤ (max r R : ℕ)+1)] at h0
      omega
    have hyr : y ∉ Box (r:ℤ) := fun h => hy (box_mono (by exact_mod_cast Nat.le_max_left r R) h)
    have hyR : y ∉ Box (R:ℤ) := fun h => hy (box_mono (by exact_mod_cast Nat.le_max_right r R) h)
    refine ⟨y,?_,hyR⟩
    apply (reach_symm (not_not.mp hx)).trans
    apply reach_mono _ (exterior_connected hd r (by positivity) b y hb hyr)
    intro z hz hzA
    exact hz (hAr hzA)
  · intro hx hH
    obtain ⟨y,hxy,hy⟩ := hx r
    have hby : Reach Aᶜ b y := by
      apply reach_mono _ (exterior_connected hd r (by positivity) b y hb hy)
      intro z hz hzA
      exact hz (hAr hzA)
    exact hH (hby.trans (reach_symm hxy))

lemma reach_preserves_hull {d : ℕ} (A : Set (Site d)) (b : Site d) {x y : Site d}
    (hxy : Reach Aᶜ x y) : x ∈ Hull A b ↔ y ∈ Hull A b := by
  constructor
  · intro hx hy
    exact hx (hy.trans (reach_symm hxy))
  · intro hy hx
    exact hy (hx.trans hxy)

lemma connected_avoids_hull {d : ℕ} (A V : Set (Site d)) (b : Site d)
    (hV : Heisenberg.LatticeCut.Connected V) (hVA : Disjoint V A)
    {x : Site d} (hx : x ∈ V) (hxH : x ∉ Hull A b) : V ⊆ (Hull A b)ᶜ := by
  intro y hy hyH
  apply hxH
  apply (reach_preserves_hull A b ?_).mpr hyH
  apply reach_mono _ (hV x hx y hy)
  intro z hz hzA
  exact Set.disjoint_left.mp hVA hz hzA

lemma hull_subset_of_subset_hull {d : ℕ} (A B : Set (Site d)) (b : Site d)
    (hAB : A ⊆ Hull B b) : Hull A b ⊆ Hull B b := by
  intro x hx
  by_contra hxB
  apply hx
  have hb : b ∈ (Hull B b)ᶜ := fun h => h (reach_refl Bᶜ b)
  have hbx := complement_connected B b b hb x hxB
  apply reach_mono _ hbx
  intro z hz hzA
  exact hz (hAB hzA)

theorem hull_laminar {d : ℕ} (A B : Set (Site d))
    (hA : Heisenberg.LatticeCut.Connected A) (hB : Heisenberg.LatticeCut.Connected B)
    (hAn : A.Nonempty) (_hBn : B.Nonempty) (hAB : Disjoint A B)
    {b : Site d} (hbA : b ∉ A) (_hbB : b ∉ B) :
    Hull A b ⊆ Hull B b ∨ Hull B b ⊆ Hull A b ∨ Disjoint (Hull A b) (Hull B b) := by
  by_cases hsubA : A ⊆ Hull B b
  · exact Or.inl (hull_subset_of_subset_hull A B b hsubA)
  by_cases hsubB : B ⊆ Hull A b
  · exact Or.inr (Or.inl (hull_subset_of_subset_hull B A b hsubB))
  obtain ⟨a,ha,haB⟩ : ∃ a ∈ A, a ∉ Hull B b := Set.not_subset.mp hsubA
  obtain ⟨c,hc,hcA⟩ : ∃ c ∈ B, c ∉ Hull A b := Set.not_subset.mp hsubB
  have hBext := connected_avoids_hull A B b hB hAB.symm hc hcA
  have hHB : Disjoint (Hull A b) B := Set.disjoint_left.mpr (fun x hx hxB => hBext hxB hx)
  have hHAext := connected_avoids_hull B (Hull A b) b (hull_connected A hA hAn hbA)
    hHB (subset_hull A hbA ha) haB
  exact Or.inr (Or.inr (Set.disjoint_left.mpr (fun x hx hxB => hHAext hx hxB)))

end Heisenberg.LatticeHull
end

end OAI
