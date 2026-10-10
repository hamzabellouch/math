import OAI.Analysis.Triangular.Construction.PeriodicJets
import OAI.Analysis.Triangular.Envelope.EnvelopeBoxes

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma residue_injective : Function.Injective residue := by decide +kernel
lemma residue_mod (a : Fin 15) : residue a % 36 = residue a := by revert a; decide +kernel
lemma residue_mem (a : Fin 15) : residue a ∈ residues := by revert a; decide +kernel
lemma finiteNode_lt25 {n : ℤ} (hn : n ∈ FiniteNodes) : n<25 := by
  simp only [FiniteNodes,Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with h|h|h|h|h|h|h|h|h|h <;> omega
lemma tailBase_node (a : Fin 15) (l : ℕ) :
    0 < tailBase a+36*l ∧ (tailBase a+36*l)%36 ∈ residues := by
  constructor
  · have hh := tailBase_pos a
    omega
  · simpa [Int.add_emod,Int.mul_emod,tailBase_mod,residue_mod] using residue_mem a

def enumerateTail (p : Fin 15 × ℕ) : TailNode :=
  ⟨⟨tailBase p.1+36*p.2,tailBase_node p.1 p.2⟩,by
    intro hh
    have hlt := finiteNode_lt25 hh
    change tailBase p.1+36*(p.2:ℤ)<25 at hlt
    have hge := tailBase_pos p.1
    omega⟩
lemma tailBase_le (n : TailNode) (a : Fin 15) (ha : n.val.val%36=residue a) :
    tailBase a ≤ n.val.val := by
  have hn := n.val.property.1
  have hf := n.property
  have hdiv := Int.emod_add_mul_ediv n.val.val 36
  have hq : 0≤n.val.val/36 := Int.ediv_nonneg hn.le (by norm_num)
  rw [ha] at hdiv
  fin_cases a <;> norm_num [tailBase,residue] at *
  all_goals by_contra hlt
  all_goals have hn' : n.val.val = (n.val.val%36) := by omega
  all_goals simp only [FiniteNodes,Finset.mem_insert,Finset.mem_singleton] at hf
  all_goals omega
lemma enumerateTail_injective : Function.Injective enumerateTail := by
  intro p q hpq
  have hh := congrArg (fun n : TailNode => n.val.val) hpq
  change tailBase p.1+36*p.2=tailBase q.1+36*q.2 at hh
  have hm := congrArg (fun n : ℤ => n%36) hh
  simp only [Int.add_emod,Int.mul_emod,Int.emod_self,zero_mul,Int.zero_emod,
    add_zero,tailBase_mod,residue_mod] at hm
  have ha := residue_injective hm
  apply Prod.ext ha
  rw [ha] at hh
  omega
lemma enumerateTail_surjective : Function.Surjective enumerateTail := by
  intro n
  obtain ⟨a,ha⟩ := node_residue n.val
  have hle := tailBase_le n a ha
  have hm : (n.val.val-tailBase a)%36=0 := by
    rw [Int.sub_emod,ha,tailBase_mod]
    simp
  have hd := Int.emod_add_mul_ediv (n.val.val-tailBase a) 36
  rw [hm,zero_add] at hd
  have hq : 0 ≤ (n.val.val-tailBase a)/36 := Int.ediv_nonneg (sub_nonneg.mpr hle) (by norm_num)
  refine ⟨(a,((n.val.val-tailBase a)/36).toNat),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change tailBase a+36*(((n.val.val-tailBase a)/36).toNat:ℤ)=n.val.val
  rw [Int.toNat_of_nonneg hq]
  omega

def tailEnumeration : (Fin 15 × ℕ) ≃ TailNode :=
  Equiv.ofBijective enumerateTail ⟨enumerateTail_injective,enumerateTail_surjective⟩
lemma Q_enumerateTail (a : Fin 15) (l : ℕ) :
    Q (enumerateTail (a,l)).val.val=Q (tailBase a) := by
  rw [Q_emod,Q_emod (tailBase a)]
  congr 1
  change (tailBase a+36*(l:ℤ))%36=tailBase a%36
  simp
lemma D_enumerateTail (a : Fin 15) (l : ℕ) :
    D (enumerateTail (a,l)).val.val=D (tailBase a) := by
  rw [D_emod,D_emod (tailBase a)]
  congr 1
  change (tailBase a+36*(l:ℤ))%36=tailBase a%36
  simp
end AtomicTriangular.Construction
end

end OAI
