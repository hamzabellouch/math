import Mathlib
import OAI.Computability.VertexCover.PCP.PreprocessingTables
import OAI.Computability.VertexCover.Analysis.GraphComplete
import OAI.Computability.VertexCover.Machines.Cardinal

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover
open Machine

namespace Approximation
variable {α : ℝ}

theorem coverNumber_le_length (A : Approximation α) (G : ExplicitGraph) :
    G.coverNumber ≤ (A.run G).length := by
  classical
  let L := (A.run G).toFinset
  let e : {n // n ∈ L} ↪ Fin G.n :=
    ⟨fun n => ⟨n.val,A.vertices G n.val (List.mem_toFinset.mp n.property)⟩,
      fun _ _ h => Subtype.ext (congrArg Fin.val h)⟩
  let S : Finset (Fin G.n) := L.attach.map e
  have memS (n : Fin G.n) (hn : n.val ∈ A.run G) : n ∈ S := by
    apply Finset.mem_map.mpr
    exact ⟨⟨n.val,List.mem_toFinset.mpr hn⟩,Finset.mem_attach _ _,Fin.ext rfl⟩
  have hc : G.Cover S := by
    intro p hp
    exact (A.covers G p hp).imp (memS p.1) (memS p.2)
  have hcard : S.card = (A.run G).length := by
    simp only [S,Finset.card_map,Finset.card_attach,L]
    exact List.toFinset_card_of_nodup (A.nodup G)
  simpa only [hcard] using ExplicitGraph.coverNumber_le S hc

noncomputable def cardPoly (A : Approximation α) :
    Machine.Poly ExplicitGraph.bits natBits (fun G => (A.run G).length) :=
  (⟨A.computation,A.finiteAlphabet⟩ : Machine.Poly ExplicitGraph.bits natListBits A.run).comp Machine.Poly.natListCard

def test (A : Approximation α) (m : ℕ) (G : ExplicitGraph) : Bool :=
  decide (m*(A.run G).length < (m-1)*G.n)

noncomputable def testPoly (A : Approximation α) (m : ℕ) :
    Machine.Poly ExplicitGraph.bits boolBits (A.test m) := by
  let lhs := ((Machine.Poly.const ExplicitGraph.bits natBits m).pair A.cardPoly).comp Machine.Poly.natMul
  let rhs := ((Machine.Poly.const ExplicitGraph.bits natBits (m-1)).pair Machine.Poly.graphCard).comp Machine.Poly.natMul
  exact (lhs.pair rhs).comp Machine.Poly.natLT

end Approximation

theorem rational_threshold (m n k : ℕ) (hm : 1 ≤ m) :
    m*k < (m-1)*n ↔ (k : ℝ) < (1-1/(m:ℝ))*(n:ℝ) := by
  have hmp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have he : (1-1/(m:ℝ))*(n:ℝ) = (((m-1:ℕ):ℝ)*n)/(m:ℝ) := by
    rw [Nat.cast_sub hm,Nat.cast_one]
    field_simp
  rw [he,lt_div_iff₀ hmp]
  rw [mul_comm (k:ℝ) (m:ℝ)]
  exact_mod_cast Iff.rfl

theorem exists_separating_integer {α : ℝ} (hα : α < 2) :
    ∃ m : ℕ, 4 ≤ m ∧ α*(1/2+1/(m:ℝ)) < 1-1/(m:ℝ) := by
  have hden : 0 < 2-α := sub_pos.mpr hα
  obtain ⟨m,hm⟩ := exists_nat_gt (max (4:ℝ) (2*(α+1)/(2-α)))
  have hm4 : 4 ≤ m := by
    have h := (le_max_left (4:ℝ) (2*(α+1)/(2-α))).trans_lt hm
    exact_mod_cast h.le
  have hb : 2*(α+1) < (m:ℝ)*(2-α) :=
    (div_lt_iff₀ hden).mp ((le_max_right (4:ℝ) _).trans_lt hm)
  have hmp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  refine ⟨m,hm4,?_⟩
  apply (mul_lt_mul_iff_left₀ hmp).mp
  have hs : (1/2+1/(m:ℝ))*(m:ℝ) = (m:ℝ)/2+1 := by field_simp
  have hn : (1-1/(m:ℝ))*(m:ℝ) = (m:ℝ)-1 := by field_simp
  rw [mul_assoc,hs,hn]
  nlinarith

noncomputable def decisionOfGap {α : ℝ} (hα : 1 ≤ α) (m : ℕ) (hm : 4 ≤ m)
    (hsep : α*(1/2+1/(m:ℝ)) < 1-1/(m:ℝ))
    (R : GapReduction m) (A : Approximation α) : ThreeSATDecision := by
  let c : Machine.Poly id boolBits (fun input => A.test m (R.construct input)) :=
    (⟨R.computation,R.finiteAlphabet⟩ : Machine.Poly id ExplicitGraph.bits R.construct).comp (A.testPoly m)
  refine ⟨fun input => A.test m (R.construct input),c.computation,c.finiteAlphabet,?_⟩
  intro input
  let G := R.construct input
  have hm1 : 1 ≤ m := by omega
  change decide (m*(A.run G).length < (m-1)*G.n)=true ↔ ThreeSAT input
  rw [decide_eq_true_eq,rational_threshold m G.n (A.run G).length hm1]
  constructor
  · intro hout
    by_contra hno
    have hlow := R.soundness input hno
    have hcover := A.coverNumber_le_length G
    have hc : (G.coverNumber:ℝ) ≤ (A.run G).length := by exact_mod_cast hcover
    exact (not_lt_of_ge hc) (lt_trans hout hlow)
  · intro hyes
    have hhigh := R.completeness input hyes
    have hcp : (0:ℝ) ≤ G.coverNumber := Nat.cast_nonneg _
    have hn : (0:ℝ) < G.n := by
      have hn0 : G.n ≠ 0 := by
        intro hz
        change (G.coverNumber:ℝ) < _ at hhigh
        rw [hz,Nat.cast_zero,mul_zero] at hhigh
        exact (not_lt_of_ge hcp) hhigh
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hαp : 0 < α := lt_of_lt_of_le zero_lt_one hα
    have hc := (A.quality G).trans_lt (mul_lt_mul_of_pos_left hhigh hαp)
    have hs := mul_lt_mul_of_pos_right hsep hn
    change ((A.run G).length : ℝ) < _
    exact hc.trans (by simpa only [mul_assoc] using hs)

end VertexCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
