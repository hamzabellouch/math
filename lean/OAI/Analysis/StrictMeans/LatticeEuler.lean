import OAI.Analysis.StrictMeans.IndexEuler

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def natEmbed (M : ℤ) (v : ℕ × ℕ) : Lattice := toLex ((v.1:ℤ)+M,(v.2:ℤ)+M)

lemma natEmbed_injective (M : ℤ) : Injective (natEmbed M) := by
  intro v w he
  have h := toLex.injective he
  apply Prod.ext <;> [have hh := congrArg Prod.fst h; have hh := congrArg Prod.snd h] <;>
    dsimp at hh <;> exact_mod_cast (add_right_cancel hh)

lemma natEmbed_x (M : ℤ) (i j : ℕ) : natEmbed M (i+1,j)=natEmbed M (i,j)+ex := by
  apply ofLex.injective
  simp [natEmbed,ex,add_assoc,add_comm]
lemma natEmbed_y (M : ℤ) (i j : ℕ) : natEmbed M (i,j+1)=natEmbed M (i,j)+ey := by
  apply ofLex.injective
  simp [natEmbed,ey,add_assoc,add_comm]
lemma natEmbed_xy (M : ℤ) (i j : ℕ) : natEmbed M (i+1,j+1)=natEmbed M (i,j)+ex+ey := by
  rw [natEmbed_x,natEmbed_y]
  abel
lemma natEmbed_mx (M : ℤ) (i j : ℕ) (hi : 0 < i) : natEmbed M (i-1,j)=natEmbed M (i,j)-ex := by
  apply eq_sub_iff_add_eq.mpr
  rw [← natEmbed_x,Nat.sub_add_cancel hi]
lemma natEmbed_my (M : ℤ) (i j : ℕ) (hj : 0 < j) : natEmbed M (i,j-1)=natEmbed M (i,j)-ey := by
  apply eq_sub_iff_add_eq.mpr
  rw [← natEmbed_y,Nat.sub_add_cancel hj]

lemma natEmbed_coverage {M : ℤ} {v : Lattice}
    (hx : M≤(ofLex v).1) (hy : M≤(ofLex v).2) : v∈range (natEmbed M) := by
  refine ⟨(((ofLex v).1-M).toNat,((ofLex v).2-M).toNat),?_⟩
  apply ofLex.injective
  simp only [natEmbed,ofLex_toLex,Int.toNat_of_nonneg (sub_nonneg.mpr hx),
    Int.toNat_of_nonneg (sub_nonneg.mpr hy),sub_add_cancel,Prod.mk.eta]

lemma finite_natEmbed_coverage {S : Set Lattice} (hS : S.Finite) :
    ∃ M : ℤ, S ⊆ range (natEmbed M) := by
  have hb := ((hS.image (fun v=>(ofLex v).1)).union
    (hS.image (fun v=>(ofLex v).2))).bddBelow
  obtain ⟨M,hM⟩ := hb
  refine ⟨M,fun v hv=>natEmbed_coverage ?_ ?_⟩
  · exact hM (Or.inl ⟨v,hv,rfl⟩)
  · exact hM (Or.inr ⟨v,hv,rfl⟩)

lemma ncard_natEmbed_preimage {M : ℤ} {S : Set Lattice}
    (hS : S ⊆ range (natEmbed M)) : (natEmbed M ⁻¹' S).ncard=S.ncard := by
  rw [← ncard_image_of_injective _ (natEmbed_injective M),image_preimage_eq_of_subset hS]

lemma lattice_sublevel_euler {u : Lattice → ℝ} {c : ℝ}
    (hfin : {v | u v≤c}.Finite) (hne : {v | u v≤c}.Nonempty)
    (hascent : ∀ v, c<u v →
      u v<u (v+ex) ∨ u v<u (v+ey) ∨ u v<u (v-ex) ∨ u v<u (v-ey)) :
    let S := hfin.toFinset
    (meshEdges S ex).card+(meshEdges S ey).card+(meshEdges S (ex+ey)).card+1 ≤
      S.card+(meshLower S ex ey).card+(meshUpper S ex ey).card := by
  classical
  obtain ⟨M,hM⟩ := finite_natEmbed_coverage hfin
  let U : ℕ × ℕ → ℝ := u ∘ natEmbed M
  let T : Set (ℕ × ℕ) := {v | U v≤c}
  let S := hfin.toFinset
  have hT : T.Finite := hfin.preimage (natEmbed_injective M).injOn
  have hTne : T.Nonempty := by
    obtain ⟨v,hv⟩ := hne
    obtain ⟨w,rfl⟩ := hM hv
    exact ⟨w,hv⟩
  have he := sublevel_euler hT hTne (u:=U) (c:=c) (by
    intro i j hc hi hj
    simpa only [U,Function.comp_apply,natEmbed_x,natEmbed_y,natEmbed_mx M i j hi,
      natEmbed_my M i j hj] using hascent (natEmbed M (i,j)) hc)
  have hV : T.ncard=S.card := by
    rw [show T=natEmbed M ⁻¹' {v | u v≤c} from rfl,ncard_natEmbed_preimage hM]
    exact Set.ncard_eq_toFinset_card _ hfin
  have hcast (K : Finset Lattice) (hKS : (K:Set Lattice)⊆{v | u v≤c}) :
      (natEmbed M ⁻¹' (K:Set Lattice)).ncard=K.card := by
    rw [ncard_natEmbed_preimage (hKS.trans hM),Set.ncard_coe_finset]
  have hH : (horizontalSet T).ncard=(meshEdges S ex).card := by
    have hh : horizontalSet T=natEmbed M ⁻¹' (meshEdges S ex:Set Lattice) := by
      ext ⟨i,j⟩
      simp [horizontalSet,meshEdges,S,T,U,natEmbed_x]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hY : (verticalSet T).ncard=(meshEdges S ey).card := by
    have hh : verticalSet T=natEmbed M ⁻¹' (meshEdges S ey:Set Lattice) := by
      ext ⟨i,j⟩
      simp [verticalSet,meshEdges,S,T,U,natEmbed_y]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hD : (diagonalSet T).ncard=(meshEdges S (ex+ey)).card := by
    have hh : diagonalSet T=natEmbed M ⁻¹' (meshEdges S (ex+ey):Set Lattice) := by
      ext ⟨i,j⟩
      simp [diagonalSet,meshEdges,S,T,U,natEmbed_xy,add_assoc]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hL : (lowerSet T).ncard=(meshLower S ex ey).card := by
    have hh : lowerSet T=natEmbed M ⁻¹' (meshLower S ex ey:Set Lattice) := by
      ext ⟨i,j⟩
      simp [lowerSet,meshLower,S,T,U,natEmbed_x,natEmbed_y,add_comm,add_left_comm,add_assoc]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hR : (upperSet T).ncard=(meshUpper S ex ey).card := by
    have hh : upperSet T=natEmbed M ⁻¹' (meshUpper S ex ey:Set Lattice) := by
      ext ⟨i,j⟩
      simp [upperSet,meshUpper,S,T,U,natEmbed_y,natEmbed_x,add_assoc]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  rw [hV,hH,hY,hD,hL,hR] at he
  exact he

lemma lattice_sublevel_index {u : Lattice → ℝ} {c : ℝ}
    (hfin : {v | u v≤c}.Finite) (hne : {v | u v≤c}.Nonempty)
    (hascent : ∀ v, c<u v →
      u v<u (v+ex) ∨ u v<u (v+ey) ∨ u v<u (v-ex) ∨ u v<u (v-ey)) :
    1≤∑ v∈hfin.toFinset, heightIndex u ex ey v := by
  have hS : ∀ a∈hfin.toFinset, ∀ b, heightRank u b<heightRank u a→b∈hfin.toFinset := by
    intro a ha b hb
    simp only [heightRank,Prod.Lex.toLex_lt_toLex] at hb
    apply hfin.mem_toFinset.mpr
    have ha' := hfin.mem_toFinset.mp ha
    rcases hb with hb|⟨hb,_⟩ <;> dsimp at ha' ⊢ <;> linarith
  have he := index_euler_sum (heightRank_injective u) hS ex_ne_zero ey_ne_zero ex_add_ey_ne_zero
  have h := lattice_sublevel_euler hfin hne hascent
  change 1≤∑ v∈hfin.toFinset, meshIndex (heightRank u) ex ey v
  rw [he]
  omega

end
end StrictInverseFirstPower.Grid

end

end OAI
