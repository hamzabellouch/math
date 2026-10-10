import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

def PrimeSource.DisjointMass (S T : PrimeSource) : Prop :=
  ∀ (p : S.Sample) (q : T.Sample), S.law.mass p≠0 → T.law.mass q≠0 → (p:ℕ)≠(q:ℕ)

theorem PrimeSource.DisjointMass.symm {S T : PrimeSource} (h : S.DisjointMass T) :
    T.DisjointMass S := by
  intro q p hq hp he
  exact h p q hp hq he.symm

theorem PrimeSource.disjointMass_of_log_lt (S T : PrimeSource)
    (h : ∀ (p : S.Sample) (q : T.Sample), S.law.mass p≠0 → T.law.mass q≠0 →
      Real.log (p:ℕ)<Real.log (q:ℕ)) : S.DisjointMass T := by
  intro p q hp hq he
  have hh := h p q hp hq
  rw [he] at hh
  exact (lt_irrefl _ hh)

namespace NominalCenterArray
variable {d : Decomposition} {k : ℕ} {L J tb : ℝ} {w : Fin k → ℝ}

theorem topSource_cell_support (C : NominalCenterArray d k L J tb w)
    (E : Finset ℕ) (hE : E.card≤2) (i : Fin 3) (p : (C.topSource E hE i).Sample)
    (hp : (C.topSource E hE i).law.mass p≠0) :
    |Real.log (p:ℕ)-(C.top i:ℝ)|<1 :=
  logCellPrimeSource_log_support _ _ _ p hp

theorem compSource_cell_support (C : NominalCenterArray d k L J tb w)
    (E : Finset ℕ) (hE : E.card≤2) (j : Fin k) (i : Fin 2)
    (p : (C.compSource E hE j i).Sample) (hp : (C.compSource E hE j i).law.mass p≠0) :
    |Real.log (p:ℕ)-(C.comp j i:ℝ)|<1 :=
  logCellPrimeSource_log_support _ _ _ p hp

theorem auxSource_log_bounds (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L)
    (hTop : favorableBlockWidth L/4≤J-2*tb ∧ J-2*tb≤4*favorableBlockWidth L)
    (hComp : ∀j, favorableBlockWidth L/4≤w j ∧ w j≤4*(2:ℝ)^k*favorableBlockWidth L)
    (E : Finset ℕ) (hE : E.card≤2) (i : AuxiliaryIndex k)
    (p : (C.auxSource E hE i).Sample) (hp : (C.auxSource E hE i).law.mass p≠0) :
    favorableBlockWidth L/200≤Real.log (p:ℕ) ∧
      Real.log (p:ℕ)≤3*(2:ℝ)^k*favorableBlockWidth L := by
  cases i with
  | inl i =>
    have he := C.top_log_support hh hTop i E (C.top_balanced i E hE).choose p hp
    refine ⟨he.1,he.2.trans ?_⟩
    have hpow : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
    have hwidth : 0≤favorableBlockWidth L := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hpow hwidth]
  | inr ji =>
    exact C.comp_log_support hh ji.1 (hComp ji.1) ji.2 E
      (C.comp_balanced ji.1 ji.2 E hE).choose p hp

theorem topSource_compSource_disjoint (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L) (hJ : 1000≤J) (hwidth : favorableBlockWidth L≤2*J)
    (htb : |tb|≤favorableBlockWidth L/16)
    (hw : ∀j,|w j-(2:ℝ)^(k-1-j.val)*J|≤J/100)
    (E : Finset ℕ) (hE : E.card≤2) (i : Fin 3) (j : Fin k) (r : Fin 2) :
    (C.topSource E hE i).DisjointMass (C.compSource E hE j r) := by
  apply PrimeSource.disjointMass_of_log_lt
  intro p q hp hq
  have htop := SourceRangeSeparation.top_log_window _ J tb _ _ hJ hwidth htb
    (C.top_nominal_near hh i) (C.topSource_cell_support E hE i p hp).le
  have hcomp := SourceRangeSeparation.compensation_log_window _ J _ (w j) _ _ hJ hwidth
    (hw j) (C.comp_nominal_near hh j r) (C.compSource_cell_support E hE j r q hq).le
  exact SourceRangeSeparation.top_lt_compensation J _ _ _ (by linarith)
    (one_le_pow₀ (by norm_num)) htop.2 hcomp

theorem compSource_compSource_disjoint (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L) (hJ : 1000≤J) (hwidth : favorableBlockWidth L≤2*J)
    (hw : ∀j,|w j-(2:ℝ)^(k-1-j.val)*J|≤J/100)
    (E : Finset ℕ) (hE : E.card≤2) (a b : Fin k) (hab : a≠b) (i r : Fin 2) :
    (C.compSource E hE a i).DisjointMass (C.compSource E hE b r) := by
  intro p q hp hq he
  have hpa := SourceRangeSeparation.compensation_log_window _ J _ (w a) _ _ hJ hwidth
    (hw a) (C.comp_nominal_near hh a i) (C.compSource_cell_support E hE a i p hp).le
  have hqb := SourceRangeSeparation.compensation_log_window _ J _ (w b) _ _ hJ hwidth
    (hw b) (C.comp_nominal_near hh b r) (C.compSource_cell_support E hE b r q hq).le
  have hne : a.val≠b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hab | hba
  · have h := SourceRangeSeparation.compensation_lt_compensation J k a.val b.val hab b.isLt
      _ _ (by linarith) hpa hqb
    rw [he] at h
    exact (lt_irrefl _ h)
  · have h := SourceRangeSeparation.compensation_lt_compensation J k b.val a.val hba a.isLt
      _ _ (by linarith) hqb hpa
    rw [he] at h
    exact (lt_irrefl _ h)

end NominalCenterArray
end Ostmann.Construction

end

end OAI
