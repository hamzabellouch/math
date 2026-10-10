import OAI.NumberTheory.Jacobsthal.Sieve.RealCoprimeResidueCount

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

def augmentedModuli {ι : Type*} (M0 : ℕ) (u : ι → ℕ) : Option ι → ℕ
  | none => M0
  | some i => u i

noncomputable def cellResidues {ι : Type*} (M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) :
    ∀ j : Option ι,Finset (ZMod (augmentedModuli M0 u j))
  | none => {v}
  | some i => affineResidues (c i) (b i) (E i)

theorem augmented_coprime {ι : Type*} (M0 : ℕ) (u : ι → ℕ)
    (h0 : ∀ i,Nat.Coprime M0 (u i)) (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    Pairwise (fun i j => Nat.Coprime (augmentedModuli M0 u i) (augmentedModuli M0 u j)) := by
  rintro (_|i) (_|j) hne
  · exact False.elim (hne rfl)
  · exact h0 j
  · exact (h0 i).symm
  · exact hu (fun h => hne (congrArg Option.some h))

theorem augmented_product {ι : Type*} [Fintype ι] (M0 : ℕ) (u : ι → ℕ) :
    (∏ j : Option ι,augmentedModuli M0 u j) = M0*∏ i,u i := by
  simp only [Fintype.prod_option,augmentedModuli]

theorem cell_card_product {ι : Type*} [Fintype ι] (M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) :
    (∏ j : Option ι,(cellResidues M0 u v c b E j).card) = ∏ i,(E i).card := by
  rw [Fintype.prod_option]
  have hbase : (cellResidues M0 u v c b E none).card = 1 := Finset.card_singleton v
  rw [hbase,one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  exact affineResidues_card (c i) (b i) (E i)

noncomputable def slopeCell {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) : Finset ℤ :=
  (Finset.Ico (0 : ℤ) (p : ℤ)).filter (fun s => (s : ZMod M0) = v ∧ ∀ i,(c i : ZMod (u i))*(s : ZMod (u i))+b i ∈ E i)

theorem slopeCell_eq_crtSlopes {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i))) :
    slopeCell p M0 u v c b E = crtSlopes 0 p (augmentedModuli M0 u) (cellResidues M0 u v c b E) := by
  ext s
  simp only [slopeCell,crtSlopes,Finset.mem_filter]
  apply and_congr_right
  intro _hs
  constructor
  · rintro ⟨hv,hE⟩ j
    cases j with
    | none => exact Finset.mem_singleton.mpr hv
    | some i => exact (mem_affineResidues (c i) (b i) (E i) (s : ZMod (u i))).mpr (hE i)
  · intro h
    exact ⟨Finset.mem_singleton.mp (h none),fun i => (mem_affineResidues (c i) (b i) (E i) (s : ZMod (u i))).mp (h (some i))⟩

theorem slopeCell_card_upper {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i)))
    (hM : 0 < M0) (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((slopeCell p M0 u v c b E).card : ℝ) ≤
      (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(M0*(∏ i,u i) : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) := by
  have hN : 0 < ∏ j : Option ι,augmentedModuli M0 u j := by
    rw [augmented_product]
    exact Nat.mul_pos hM (Finset.prod_pos (fun i _ => hU i))
  have hh := crt_initial_count_upper p (augmentedModuli M0 u) (augmented_coprime M0 u h0 hu)
    (cellResidues M0 u v c b E) hN
  rw [← slopeCell_eq_crtSlopes,augmented_product,cell_card_product] at hh
  exact hh

end ErdosInverseCRT

end

end Erdos970

end OAI
