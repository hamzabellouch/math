import OAI.Analysis.MarkovType.SpreadingModel
import OAI.Analysis.MarkovType.SubdivisionProfiles
import OAI.Analysis.MarkovType.SubdivisionSpreading
import OAI.Analysis.MarkovType.AntitoneSeminormLimit

namespace OAI

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MarkovSuperreflexivity

namespace Subdivision

theorem subdivide_le_ofArray (p : Seminorm ℝ C00)
    (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a, p (C00.place ι a) = p (C00.ofArray a))
    {m : ℕ} (a : Fin m → ℝ) (J M : ℕ → ℕ)
    (hJ : ∀ i : Fin m, 0 < J i.val) (hJM : ∀ i : Fin m, J i.val ≤ M i.val) :
    p (C00.subdivide M (C00.ofArray a)) ≤ p (C00.subdivide J (C00.ofArray a)) := by
  rw [C00.subdivide_ofArray_eq_finiteSubdivision, C00.subdivide_ofArray_eq_finiteSubdivision]
  exact finiteSubdivision_mono p hspread a _ _ hJ hJM

theorem subdivide_le (p : Seminorm ℝ C00)
    (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a, p (C00.place ι a) = p (C00.ofArray a))
    (J M : ℕ → ℕ) (hJ : ∀ i, 0 < J i) (hJM : ∀ i, J i ≤ M i) (x : C00) :
    p (C00.subdivide M x) ≤ p (C00.subdivide J x) := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha]
  exact subdivide_le_ofArray p hspread a J M (fun i => hJ i.val) (fun i => hJM i.val)

end Subdivision

namespace SpreadingModel

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def subdivisionFamily (S : SpreadingModel Y) (n : ℕ) : Seminorm ℝ C00 :=
  S.p.comp (C00.uniformSubdivision (n + 1))

theorem subdivisionFamily_antitone (S : SpreadingModel Y) (x : C00) :
    Antitone fun n => S.subdivisionFamily n x := by
  intro n m hnm
  exact Subdivision.subdivide_le S.p S.spreading (fun _ => n + 1) (fun _ => m + 1)
    (fun _ => Nat.succ_pos n) (fun _ => Nat.succ_le_succ hnm) x

def averagedSeminorm (S : SpreadingModel Y) : Seminorm ℝ C00 :=
  SeminormLimit.seminorm S.subdivisionFamily S.subdivisionFamily_antitone

theorem tendsto_averagedSeminorm (S : SpreadingModel Y) (x : C00) :
    Tendsto (fun n => S.p (C00.uniformSubdivision (n + 1) x)) atTop
      (𝓝 (S.averagedSeminorm x)) :=
  SeminormLimit.tendsto_value S.subdivisionFamily S.subdivisionFamily_antitone x

theorem averaged_le_uniform (S : SpreadingModel Y) (x : C00)
    (q : ℕ) (hq : 0 < q) :
    S.averagedSeminorm x ≤ S.p (C00.uniformSubdivision q x) := by
  unfold averagedSeminorm
  have h := SeminormLimit.seminorm_le S.subdivisionFamily
    S.subdivisionFamily_antitone x (q - 1)
  have he : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  simpa only [subdivisionFamily, Seminorm.comp_apply, he] using h

theorem p_le_l1Mass (S : SpreadingModel Y) (x : C00) : S.p x ≤ C00.l1Mass x := by
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  rw [← ha, C00.l1Mass_ofArray]
  exact S.array_upper a

theorem subdivisionFamily_upper (S : SpreadingModel Y) (n : ℕ) (x : C00) :
    S.subdivisionFamily n x ≤ C00.l1Mass x := by
  change S.p (C00.uniformSubdivision (n + 1) x) ≤ C00.l1Mass x
  have h := S.p_le_l1Mass (C00.uniformSubdivision (n + 1) x)
  simpa only [C00.l1Mass_uniformSubdivision (n + 1) (Nat.succ_pos n)] using h

theorem subdivisionFamily_prefix_lower (S : SpreadingModel Y) (n : ℕ)
    (x : C00) (k : ℕ) : S.d * |prefixCut x k| ≤ S.subdivisionFamily n x := by
  change S.d * |prefixCut x k| ≤ S.p (C00.uniformSubdivision (n + 1) x)
  have h := S.prefix_lower (C00.uniformSubdivision (n + 1) x) ((n + 1) * k)
  simpa only [C00.prefixCut_uniformSubdivision (n + 1) (Nat.succ_pos n)] using h

theorem averaged_prefix_lower (S : SpreadingModel Y) (x : C00) (k : ℕ) :
    S.d * |prefixCut x k| ≤ S.averagedSeminorm x :=
  SeminormLimit.prefix_lower S.subdivisionFamily S.subdivisionFamily_antitone S.d
    S.subdivisionFamily_prefix_lower x k

theorem averaged_array_upper (S : SpreadingModel Y) {m : ℕ} (a : Fin m → ℝ) :
    S.averagedSeminorm (C00.ofArray a) ≤ ∑ i, |a i| := by
  unfold averagedSeminorm
  have h := SeminormLimit.upper_bound S.subdivisionFamily S.subdivisionFamily_antitone
    (C00.ofArray a) (fun n => S.subdivisionFamily_upper n (C00.ofArray a))
  simpa only [C00.l1Mass_ofArray] using h

theorem averaged_coordinate_lower (S : SpreadingModel Y) (x : C00) (i : ℕ) :
    (S.d / 2) * |x i| ≤ S.averagedSeminorm x :=
  SpreadingLimit.coordinate_lower_of_prefix S.averagedSeminorm S.d S.d_pos.le
    S.averaged_prefix_lower x i

theorem averaged_definite (S : SpreadingModel Y) (x : C00) :
    S.averagedSeminorm x = 0 → x = 0 :=
  SeminormLimit.definite S.subdivisionFamily S.subdivisionFamily_antitone S.d_pos
    S.subdivisionFamily_prefix_lower x

theorem averaged_spreading (S : SpreadingModel Y) {m : ℕ}
    (ι : Fin m → ℕ) (hι : StrictMono ι) (a : Fin m → ℝ) :
    S.averagedSeminorm (C00.place ι a) = S.averagedSeminorm (C00.ofArray a) :=
  SeminormLimit.spreading S.subdivisionFamily S.subdivisionFamily_antitone
    (fun n => Subdivision.uniform_spreading S.p S.spreading (n + 1) (Nat.succ_pos n))
    ι hι a

theorem averaged_subdivide (S : SpreadingModel Y) (J : ℕ → ℕ)
    (hJ : ∀ i, 0 < J i) (x : C00) :
    S.averagedSeminorm (C00.subdivide J x) = S.averagedSeminorm x := by
  classical
  obtain ⟨m, a, ha⟩ := C00.exists_ofArray x
  subst x
  let K : ℕ := (∑ i : Fin m, J i.val) + 1
  have hK : 0 < K := Nat.succ_pos _
  have hJK (i : Fin m) : J i.val ≤ K := by
    have hle : J i.val ≤ ∑ j : Fin m, J j.val :=
      Finset.single_le_sum (f := fun j : Fin m => J j.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact hle.trans (Nat.le_succ _)
  have hlo (n : ℕ) : S.averagedSeminorm (C00.ofArray a) ≤
      S.p (C00.uniformSubdivision (n + 1) (C00.subdivide J (C00.ofArray a))) := by
    rw [C00.uniformSubdivision_subdivide (n + 1) (Nat.succ_pos n) J hJ]
    apply (S.averaged_le_uniform (C00.ofArray a) ((n + 1) * K)
      (Nat.mul_pos (Nat.succ_pos n) hK)).trans
    exact Subdivision.subdivide_le_ofArray S.p S.spreading a
      (fun i => (n + 1) * J i) (fun _ => (n + 1) * K)
      (fun i => Nat.mul_pos (Nat.succ_pos n) (hJ i.val))
      (fun i => Nat.mul_le_mul_left (n + 1) (hJK i))
  have hhi (n : ℕ) :
      S.p (C00.uniformSubdivision (n + 1) (C00.subdivide J (C00.ofArray a))) ≤
        S.p (C00.uniformSubdivision (n + 1) (C00.ofArray a)) := by
    rw [C00.uniformSubdivision_subdivide (n + 1) (Nat.succ_pos n) J hJ]
    apply Subdivision.subdivide_le_ofArray S.p S.spreading a
      (fun _ => n + 1) (fun i => (n + 1) * J i)
      (fun _ => Nat.succ_pos n)
    intro i
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (n + 1) (Nat.succ_le_of_lt (hJ i.val))
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto'
      (S.tendsto_averagedSeminorm (C00.subdivide J (C00.ofArray a)))
      (S.tendsto_averagedSeminorm (C00.ofArray a)) hhi
  · exact ge_of_tendsto'
      (S.tendsto_averagedSeminorm (C00.subdivide J (C00.ofArray a))) hlo

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
