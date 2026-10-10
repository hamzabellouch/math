import OAI.NumberTheory.ShortEgyptian.GreedyPreparation

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma dense_split_nat (G : Finset ℕ) (N n : ℕ) (hn : n ≤ N)
    (hbad : 2*(Icc 1 N \ G).card < n-1) :
    ∃ u ∈ G, ∃ v ∈ G, n=u+v := by
  by_contra h
  let B := Ico 1 n \ G
  have hcov : Ico 1 n ⊆ B ∪ B.image (n-·) := by
    intro u hu
    by_cases huG : u ∈ G
    · have huv := mem_Ico.mp hu
      have hv : n-u ∉ G := by
        intro hv
        exact h ⟨u,huG,n-u,hv,by omega⟩
      have hvB : n-u ∈ B := mem_sdiff.mpr ⟨mem_Ico.mpr (by omega),hv⟩
      exact mem_union.mpr (Or.inr (mem_image.mpr ⟨n-u,hvB,by omega⟩))
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hu,huG⟩))
  have hB : B ⊆ Icc 1 N \ G := by
    intro u hu
    obtain ⟨hu,huG⟩ := mem_sdiff.mp hu
    obtain ⟨hu1,hun⟩ := mem_Ico.mp hu
    exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hu1,le_trans hun.le hn⟩,huG⟩
  have hh := (card_le_card hcov).trans ((card_union_le B (B.image (n-·))).trans
    (add_le_add (card_le_card hB) ((card_image_le).trans (card_le_card hB))))
  rw [Nat.card_Ico] at hh
  omega

lemma dense_split (X : ℝ) (hX : 4<X) (G : Finset ℕ) (n : ℕ)
    (hnlo : X/2 ≤ n) (hnhi : (n:ℝ) ≤ X)
    (hbad : ((Icc 1 ⌊X⌋₊ \ G).card:ℝ) ≤ X/8) :
    ∃ u ∈ G, ∃ v ∈ G, n=u+v := by
  have hnpos : 1≤n := by
    have hh : (1:ℝ)≤n := by linarith
    exact_mod_cast hh
  apply dense_split_nat G ⌊X⌋₊ n (Nat.le_floor hnhi)
  have hh : (2:ℝ)*((Icc 1 ⌊X⌋₊ \ G).card:ℝ) < (n:ℝ)-1 := by linarith
  have hh' : ((2*(Icc 1 ⌊X⌋₊ \ G).card:ℕ):ℝ) < ((n-1:ℕ):ℝ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hnpos,Nat.cast_one] using hh
  exact_mod_cast hh'

lemma floor_multiple (X : ℝ) (P : ℕ) (hP : 0<P) (hPX : (P:ℝ)≤X) :
    let g := ⌊X/(P:ℝ)⌋₊
    0<g ∧ X/2 ≤ ((g*P:ℕ):ℝ) ∧ ((g*P:ℕ):ℝ)≤X := by
  dsimp
  have hPR : (0:ℝ)<P := by exact_mod_cast hP
  have hx : 1≤X/(P:ℝ) := (le_div_iff₀ hPR).mpr (by simpa using hPX)
  have hg : 0<⌊X/(P:ℝ)⌋₊ := Nat.floor_pos.mpr hx
  have hgR : (1:ℝ) ≤ ⌊X/(P:ℝ)⌋₊ := by exact_mod_cast hg
  have hi := Nat.lt_floor_add_one (X/(P:ℝ))
  have hlo : X/(P:ℝ) ≤ 2*(⌊X/(P:ℝ)⌋₊:ℝ) := by linarith
  have hhi := Nat.floor_le (show 0≤X/(P:ℝ) by linarith)
  have hlo' := (div_le_iff₀ hPR).mp hlo
  have hhi' := (le_div_iff₀ hPR).mp hhi
  refine ⟨hg,?_,?_⟩ <;> push_cast <;> nlinarith

lemma isUnitSum_append {x y : ℚ} {xs ys : List ℕ}
    (hx : IsUnitSum x xs) (hy : IsUnitSum y ys) : IsUnitSum (x+y) (xs++ys) := by
  refine ⟨?_,?_⟩
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hx.1 n hn
    · exact hy.1 n hn
  · rw [unitSum_append,hx.2,hy.2]

lemma isUnitSum_scale {x : ℚ} {xs : List ℕ} (h : IsUnitSum x xs)
    (g : ℕ) (hg : 0<g) : IsUnitSum (x/(g:ℚ)) (xs.map (g*·)) := by
  refine ⟨?_,?_⟩
  · intro n hn
    obtain ⟨m,hm,hmn⟩ := List.mem_map.mp hn
    subst n
    have hh := h.1 m hm
    nlinarith
  · rw [unitSum_scale,h.2]

end ShortEgyptian

end OAI
