import OAI.Analysis.PlanarPacking.TableDensityBase
import OAI.Analysis.PlanarPacking.Certificate.TableList

namespace OAI

/-!
# Cardinal densities and finite coefficient families

The finite coefficient densities agree with the cardinal densities of the corresponding data.
-/

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma tableRaw_offnode {n : ℕ} (hn : n%12 ∉ residues) : tableRaw n=(0,0,0,0) := by
  unfold tableRaw
  split <;> (first | (solve | norm_num [residues] at hn) | rfl)
lemma tableC_offnode (a : Bool) {n : ℕ} (hn : n%12 ∉ residues) : tableC a n=0 := by
  have hn0 : n≠0 := by intro h; subst n; norm_num [residues] at hn
  simp [tableC,tableRaw_offnode hn,hn0]
lemma tableD_offnode (a : Bool) {n : ℕ} (hn : n%12 ∉ residues) : tableD a n=0 := by
  have hn0 : n≠0 := by intro h; subst n; norm_num [residues] at hn
  simp [tableD,tableRaw_offnode hn,hn0]
lemma tableData_density (a : Bool) (j : ℕ) (t : ℝ) :
    density (tableData a) j t = tableDensity a j t := by
  classical
  let term (n : ℕ) : ℂ := ((tableC a n:ℝ):ℂ)*u n j t+((tableD a n:ℝ):ℂ)*v n j t
  have hz : ∀ n ∉ Finset.range 101, term n=0 := by
    intro n hn
    have hn' : 100<n := by have hh := Finset.mem_range.not.mp hn; omega
    simp [term,tableC_large a hn',tableD_large a hn']
  have ht : (∑' n : Node, term n.val)=∑' n : ℕ, if n=0 then 0 else term n := by
    have he : (∑' n : Node, term n.val) =
        ∑' n : Node, (if n.val=0 then 0 else term n.val) := by
      apply tsum_congr
      intro n
      rw [ite_eq_right (Nat.ne_of_gt n.property.1)]
    rw [he]
    apply tsum_subtype_eq_of_support_subset (s := {n : ℕ | 0<n ∧ n%12∈residues}) (f := fun n => if n=0 then 0 else term n)
    intro n hn
    by_cases hn0 : n=0
    · subst n; simp at hn
    have hnp : 0<n := Nat.pos_of_ne_zero hn0
    refine ⟨hnp,?_⟩
    by_contra hh
    exact hn (by simp [hn0,term,tableC_offnode a hh,tableD_offnode a hh])
  have he : ∑' n : ℕ, (if n=0 then 0 else term n) =
      ∑ n ∈ (Finset.range 101).erase 0,term n := by
    rw [tsum_eq_sum (s := (Finset.range 101).erase 0) (by
      intro n hn
      by_cases hn0 : n=0
      · simp [hn0]
      · rw [ite_eq_right hn0]
        apply hz
        simpa only [Finset.mem_erase,hn0,ne_eq,not_false_eq_true,true_and] using hn)]
    apply Finset.sum_congr rfl
    intro n hn
    exact ite_eq_right (Finset.ne_of_mem_erase hn)
  change term 0+(∑' n : Node,term n.val)=_
  rw [ht,he,add_comm,Finset.sum_erase_add _ _ (by simp)]
  rfl
end SharpPlanar

end OAI
