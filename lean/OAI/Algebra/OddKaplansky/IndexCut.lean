import OAI.Algebra.OddKaplansky.Cellular

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.IndexCut
variable {S : Type portUniverse1} {L : Type portUniverse2} {r n : ℕ} (s : S ≃ Fin r) (l : L ≃ Fin n) (hn : r < n)
def inclusion (i : S) : L := l.symm (Fin.castLE hn.le (s i))
lemma injective : Function.Injective (inclusion s l hn) := by
  intro i j he
  apply s.injective
  apply Fin.ext
  have hh := congrArg (fun x => (l x).val) he
  simpa only [inclusion,Equiv.apply_symm_apply,Fin.val_castLE] using hh
def extra : L := l.symm ⟨n-1,by omega⟩
lemma misses (i : S) : inclusion s l hn i ≠ extra l hn := by
  intro he
  have hh := congrArg (fun x => (l x).val) he
  simp only [inclusion,extra,Equiv.apply_symm_apply,Fin.val_castLE] at hh
  have hi := (s i).isLt
  omega
end OddKaplansky.IndexCut

end

end OAI
