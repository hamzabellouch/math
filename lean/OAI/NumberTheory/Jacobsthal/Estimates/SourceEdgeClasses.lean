import OAI.NumberTheory.Jacobsthal.Partitions.SlopeCellPartition

namespace OAI

namespace Erdos970

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem product_density {ι : Type*} [Fintype ι] (u : ι → ℕ) (E : ∀ i,Finset (ZMod (u i))) :
    ((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,u i : ℕ) = ∏ i,((E i).card : ℝ)/(u i : ℝ) := by
  push_cast
  rw [Finset.prod_div_distrib]

theorem slopeCell_normalized_upper {ι : Type*} [Fintype ι] (p M0 : ℕ) (u : ι → ℕ) (v : ZMod M0)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i)) (E : ∀ i,Finset (ZMod (u i)))
    (hM : 0 < M0) (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((slopeCell p M0 u v c b E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∏ i,((E i).card : ℝ)/(u i : ℝ))+((∏ i,u i : ℕ) : ℝ) := by
  have hcR : ((∏ i,(E i).card : ℕ) : ℝ) ≤ ((∏ i,u i : ℕ) : ℝ) :=
    Nat.cast_le.mpr (product_card_le_moduli u E hU)
  calc
    _ ≤ (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(M0*(∏ i,u i) : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) :=
      slopeCell_card_upper p M0 u v c b E hM hU h0 hu
    _ ≤ (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(M0*(∏ i,u i) : ℕ)+((∏ i,u i : ℕ) : ℝ) :=
      add_le_add le_rfl hcR
    _ = (p : ℝ)/(M0 : ℝ)*(((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,u i : ℕ))+((∏ i,u i : ℕ) : ℝ) := by
      push_cast
      ring
    _ = _ := by rw [product_density]

theorem sampledSlopes_card_upper {ι : Type*} [Fintype ι] (p M0 : ℕ) [NeZero M0] (u : ι → ℕ)
    (c : ∀ i,(ZMod (u i))ˣ) (b : ∀ i,ZMod (u i))
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i)))
    (hU : ∀ i,0 < u i) (h0 : ∀ i,Nat.Coprime M0 (u i))
    (hu : Pairwise (fun i j => Nat.Coprime (u i) (u j))) :
    ((sampledSlopes p M0 u c b E).card : ℝ) ≤
      (p : ℝ)/(M0 : ℝ)*(∑ v : ZMod M0,∏ i,((E v i).card : ℝ)/(u i : ℝ))+
        (M0 : ℝ)*((∏ i,u i : ℕ) : ℝ) := by
  have hM : 0 < M0 := Nat.pos_of_ne_zero (NeZero.ne M0)
  calc
    _ = ∑ v : ZMod M0,((slopeCell p M0 u v c b (E v)).card : ℝ) := by
      exact_mod_cast sampledSlopes_card p M0 u c b E
    _ ≤ ∑ v : ZMod M0,((p : ℝ)/(M0 : ℝ)*(∏ i,((E v i).card : ℝ)/(u i : ℝ))+((∏ i,u i : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun v _ => slopeCell_normalized_upper p M0 u v c b (E v) hM hU h0 hu)
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,ZMod.card]

end ErdosInverseCRT

end

section

namespace ErdosInverseCRT
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def sourceEdgeResidue (p q u : ℕ) (hp : Nat.Coprime p u) (hq : Nat.Coprime q u)
    (a b s : ℤ) : ZMod u :=
  ((a : ZMod u)-(b : ZMod u)-(q : ZMod u)*(s : ZMod u))*
    (↑((ZMod.unitOfCoprime p hp*ZMod.unitOfCoprime q hq)⁻¹) : ZMod u)

noncomputable def sourceCoefficient (p u : ℕ) (hp : Nat.Coprime p u) : (ZMod u)ˣ :=
  -(ZMod.unitOfCoprime p hp)⁻¹

noncomputable def sourceShift (p q u : ℕ) (hp : Nat.Coprime p u) (hq : Nat.Coprime q u)
    (a b : ℤ) : ZMod u :=
  ((a : ZMod u)-(b : ZMod u))*(↑((ZMod.unitOfCoprime p hp*ZMod.unitOfCoprime q hq)⁻¹) : ZMod u)

theorem sourceEdgeResidue_eq_affine (p q u : ℕ) (hp : Nat.Coprime p u) (hq : Nat.Coprime q u)
    (a b s : ℤ) : sourceEdgeResidue p q u hp hq a b s =
      (sourceCoefficient p u hp : ZMod u)*(s : ZMod u)+sourceShift p q u hp hq a b := by
  have hh := source_edge_class_affine (ZMod.unitOfCoprime p hp) (ZMod.unitOfCoprime q hq)
    (a : ZMod u) (b : ZMod u) (s : ZMod u)
  simpa only [sourceEdgeResidue,sourceCoefficient,sourceShift,ZMod.coe_unitOfCoprime] using hh

theorem sourceEdgeResidue_of_same_cell (p q q0 u : ℕ) (hp : Nat.Coprime p u)
    (hq : Nat.Coprime q u) (hq0 : Nat.Coprime q0 u) (a b b0 s : ℤ)
    (hqq : (q : ZMod u) = (q0 : ZMod u)) (hbb : (b : ZMod u) = (b0 : ZMod u)) :
    sourceEdgeResidue p q u hp hq a b s = sourceEdgeResidue p q0 u hp hq0 a b0 s := by
  have he : ZMod.unitOfCoprime q hq = ZMod.unitOfCoprime q0 hq0 := by
    apply Units.ext
    simpa only [ZMod.coe_unitOfCoprime] using hqq
  unfold sourceEdgeResidue
  rw [hqq,hbb,he]

theorem source_progression_edge_hit (p q u : ℕ) (hp : Nat.Coprime p u) (hq : Nat.Coprime q u)
    (a b s j : ℤ) :
    (((b+(q : ℤ)*(s+(p : ℤ)*j) : ℤ) : ZMod u) = (a : ZMod u)) ↔
      (j : ZMod u) = sourceEdgeResidue p q u hp hq a b s := by
  unfold sourceEdgeResidue
  rw [Units.eq_mul_inv_iff_mul_eq]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Units.val_mul,ZMod.coe_unitOfCoprime]
  constructor <;> intro h <;> linear_combination h

noncomputable def sourceTestedSlopes {ι : Type*} [Fintype ι] (p q0 M0 : ℕ) (u : ι → ℕ)
    (hp : ∀ i,Nat.Coprime p (u i)) (hq : ∀ i,Nat.Coprime q0 (u i)) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) : Finset ℤ :=
  (Finset.Ico (0 : ℤ) (p : ℤ)).filter
    (fun s => ∀ i,sourceEdgeResidue p q0 (u i) (hp i) (hq i) (a (u i)) b0 s ∈ E (s : ZMod M0) i)

theorem sourceTestedSlopes_eq_sampledSlopes {ι : Type*} [Fintype ι] (p q0 M0 : ℕ) (u : ι → ℕ)
    (hp : ∀ i,Nat.Coprime p (u i)) (hq : ∀ i,Nat.Coprime q0 (u i)) (a : ℕ → ℤ) (b0 : ℤ)
    (E : ZMod M0 → ∀ i,Finset (ZMod (u i))) :
    sourceTestedSlopes p q0 M0 u hp hq a b0 E = sampledSlopes p M0 u
      (fun i => sourceCoefficient p (u i) (hp i))
      (fun i => sourceShift p q0 (u i) (hp i) (hq i) (a (u i)) b0) E := by
  ext s
  simp only [sourceTestedSlopes,sampledSlopes,Finset.mem_filter,sourceEdgeResidue_eq_affine]

end ErdosInverseCRT

end

end Erdos970

end OAI
