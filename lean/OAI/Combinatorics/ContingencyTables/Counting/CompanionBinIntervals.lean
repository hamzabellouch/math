import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleJointLaw
import OAI.Combinatorics.ContingencyTables.Transport.FiniteScaledDraw
import OAI.Combinatorics.ContingencyTables.Transport.RationalMapProducts

namespace OAI

/-! # Explicit integer intervals inside the companion evaluator bins -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def intervalSize (K N beta : ℕ) : ℕ :=
  FairBits.endpoint K N (beta+1)-FairBits.endpoint K N beta

/-- Each offset is sent to its integer by adding the exact lower ceiling
endpoint. This is the actual source interval, not a cardinality-only choice. -/
def intervalEquiv (K N beta : ℕ) (hK : 0 < K) (hN : 0 < N) (hb : beta < K) :
    Fin (intervalSize K N beta) ≃ {z : ℕ // z∈FairBits.fiber K N beta} where
  toFun x := ⟨FairBits.endpoint K N beta+x.val,by
    rw [FairBits.fiber_eq_interval hK hN hb,Finset.mem_Ico]
    have hh := x.isLt
    unfold intervalSize at hh
    omega⟩
  invFun x := ⟨x.val-FairBits.endpoint K N beta,by
    have hx : FairBits.endpoint K N beta ≤ x.val ∧
        x.val < FairBits.endpoint K N (beta+1) := by
      simpa only [FairBits.fiber_eq_interval hK hN hb,Finset.mem_Ico] using x.property
    unfold intervalSize
    omega⟩
  left_inv x := by apply Fin.ext; simp
  right_inv x := by
    apply Subtype.ext
    have hx : FairBits.endpoint K N beta ≤ x.val ∧
        x.val < FairBits.endpoint K N (beta+1) := by
      simpa only [FairBits.fiber_eq_interval hK hN hb,Finset.mem_Ico] using x.property
    dsimp only
    omega

def binSize (A : Instance I J) (K : ℕ) (v : Grid (I := Fin (dimension A)) K)
    (i : Fin (dimension A)) : ℕ :=
  intervalSize K (freeRange A (index A i)) (naturalBin A v (index A i))

theorem binSize_positive (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) (i : Fin (dimension A)) :
    0 < binSize A K v i := by
  have hp := CompanionBinPopulation.coordinate_nonempty K (freeRange A (index A i)) A.d
    (naturalBin A v (index A i)) hK A.hd (by
      have hb := (A.hlarge (index A i).val.1 (index A i).val.2 (index A i).property.1).1
      unfold freeRange
      omega) (naturalBin_lt A v (index A i))
  have hc := Finset.card_pos.mpr hp
  have hN : 0 < freeRange A (index A i) := Nat.succ_pos _
  rw [FairBits.fiber_card hK hN (naturalBin_lt A v (index A i))] at hc
  exact hc

def binOffsetsEquiv (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    ((i : Fin (dimension A)) → Fin (binSize A K v i)) ≃ {f // f∈integerFiber A K hK v} :=
  (Equiv.piCongrRight (fun i => intervalEquiv K (freeRange A (index A i))
    (naturalBin A v (index A i)) hK (Nat.succ_pos _) (naturalBin_lt A v (index A i)))).trans
    ((Equiv.piCongrLeft (fun t : FreeCell A.small A.T =>
      {z : ℕ // z∈FairBits.fiber K (freeRange A t) (naturalBin A v t)}) (index A)).trans
      (integerFiberEquiv A K hK v).symm)

def binOffsetValue (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K)
    (x : (i : Fin (dimension A)) → Fin (binSize A K v i)) : FreeIndex A.small A.T A.b :=
  (binOffsetsEquiv A K hK v x).val

lemma binOffsetValue_mem (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K)
    (x : (i : Fin (dimension A)) → Fin (binSize A K v i)) :
    binOffsetValue A K hK v x∈integerFiber A K hK v := (binOffsetsEquiv A K hK v x).property

def exactBinLaw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) : RationalLaw (FreeIndex A.small A.T A.b) :=
  mapLaw (piLaw (fun i => FairBits.uniformIntLaw (binSize A K v i) (binSize_positive A K hK hW v i)))
    (binOffsetValue A K hK v)

def approximateBinLaw (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (h : ℕ) : RationalLaw (FreeIndex A.small A.T A.b) :=
  mapLaw (piLaw (fun i => FairBits.scaledLaw (binSize A K v i)
    (FairBits.offsetBitLength (binSize A K v i) h A.d) (binSize_positive A K hK hW v i)))
    (binOffsetValue A K hK v)

theorem exactBinLaw_mass (A : Instance I J) (K : ℕ) (hK : 0 < K) (hW : 100*A.d*K ≤ A.W)
    (v : Grid (I := Fin (dimension A)) K) (f : FreeIndex A.small A.T A.b) :
    (exactBinLaw A K hK hW v).mass f=
      if integerBin A K hK f=v then 1/((integerFiber A K hK v).card:ℚ) else 0 := by
  let : ∀ i : Fin (dimension A),Nonempty (Fin (binSize A K v i)) :=
    fun i => ⟨⟨0,binSize_positive A K hK hW v i⟩⟩
  let : Nonempty {f // f∈integerFiber A K hK v} :=
    ⟨⟨(integerFiber_nonempty A K hK hW v).choose,(integerFiber_nonempty A K hK hW v).choose_spec⟩⟩
  have hi (i : Fin (dimension A)) :
      FairBits.uniformIntLaw (binSize A K v i) (binSize_positive A K hK hW v i)=
        uniformLaw (α := Fin (binSize A K v i)) := by
    apply RationalLaw.ext
    funext x
    simp only [FairBits.uniformIntLaw,uniformLaw,uniformMass,Fintype.card_fin]
  unfold exactBinLaw
  simp_rw [hi]
  rw [pi_uniformLaw]
  change (mapLaw (uniformLaw (α := (i : Fin (dimension A)) → Fin (binSize A K v i)))
    (fun x => (binOffsetsEquiv A K hK v x).val)).mass f=_
  rw [←FairBits.map_equiv (binOffsetsEquiv A K hK v),FairBits.uniform_equiv]
  change (∑ x : {g // g∈integerFiber A K hK v},
    if x.val=f then (1:ℚ)/Fintype.card {g // g∈integerFiber A K hK v} else 0)=_
  rw [Fintype.card_coe]
  by_cases hf : integerBin A K hK f=v
  · rw [ite_eq_left hf]
    let g : {g // g∈integerFiber A K hK v} := ⟨f,by simp only [integerFiber,Finset.mem_filter,
      Finset.mem_univ,true_and,hf]⟩
    have he (x : {g // g∈integerFiber A K hK v}) : x.val=f ↔ x=g := by
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp_rw [he]
    simp
  · rw [ite_eq_right hf]
    apply Finset.sum_eq_zero
    intro x _
    have hxf : x.val≠f := by
      intro he
      have hx := (Finset.mem_filter.mp x.property).2
      rw [he] at hx
      exact hf hx
    simp only [hxf,ite_false]

/-- The explicitly shifted bounded quotient draws have a uniform error
bound for every bin, including the case of no free coordinates. -/
theorem approximateBinLaw_variation (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) (h : ℕ) :
    variation (approximateBinLaw A K hK hW v h) (exactBinLaw A K hK hW v) ≤
      (A.d:ℚ)/(2:ℚ)^(4*(h+A.d)) := by
  apply (variation_map _ _ (binOffsetValue A K hK v)).trans
  exact FairBits.dense_offset_product_variation (dimension A) h A.d (binSize A K v)
    (binSize_positive A K hK hW v) (ForestScaledPenalty.free_card_le A)

end

end ContingencyTables.CompanionOracleDensity

end OAI
