import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Expression
import OAI.Probability.LogConcave.OraclePrograms.SeedProgram

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open MeasureTheory Program Expression
open scoped Classical BigOperators

variable {d : ℕ}

structure ReservedProgram (d : ℕ) where
  slots : ℕ
  calls : ℕ
  pre : Program (Point d × (Fin slots → Point d)) d calls (Point d)
  shift : Fin slots → ℝ
  reserve : ℝ

namespace ReservedProgram

def full (S : ReservedProgram d) : SeedProgram d where
  slots := S.slots+1
  calls := S.calls
  program := (S.pre.seedMap (fun z : Point d × (Fin (S.slots+1) → Point d) =>
    (z.1,fun i => z.2 (Fin.castAdd 1 i))) (by fun_prop)).map
    (fun z => z.2+S.reserve • z.1.2 (Fin.natAdd S.slots 0)) (by fun_prop)
  shift := Fin.append S.shift (fun _ => 0)

lemma full_run (S : ReservedProgram d) (V : Point d → ℝ)
    (x : Point d) (g : Fin (S.slots+1) → Point d) :
    S.full.program.run V (x,g)=
      S.pre.run V (x,fun i => g (Fin.castAdd 1 i))+S.reserve • g (Fin.natAdd S.slots 0) := by
  change ((S.pre.seedMap (fun z : Point d × (Fin (S.slots+1) → Point d) =>
    (z.1,fun i => z.2 (Fin.castAdd 1 i))) (by fun_prop)).map
    (fun z => z.2+S.reserve • z.1.2 (Fin.natAdd S.slots 0)) (by fun_prop)).run V (x,g)=_
  rw [Program.map_run,Program.seedMap_run]

def extraShift (S : ReservedProgram d) (c : ℝ) : Fin (S.slots+1) → ℝ :=
  Fin.append S.shift (fun _ => c)

lemma full_equivariant (S : ReservedProgram d) (r c : ℝ) (Δ : Point d)
    (hS : S.pre.Equivariant (moveSeed (fun x => x+r • Δ) S.shift Δ) (fun y => y-Δ)) :
    S.full.program.Equivariant
      (moveSeed (fun x => x+r • Δ) (S.extraShift c) Δ)
      (fun y => y-Δ+(S.reserve*c) • Δ) := by
  dsimp only [full]
  apply Program.Equivariant.map
    (hS.seedMap _ (by fun_prop) _ ?_) _ (by fun_prop) _
  · intro z y
    simp only [moveSeed,extraShift,shiftSlots,Fin.append_right]
    simp only [smul_add,smul_smul]
    abel
  · intro z
    apply Prod.ext
    · rfl
    · funext i
      simp [moveSeed,extraShift,shiftSlots]

lemma extraShift_energy (S : ReservedProgram d) (c : ℝ) :
    (∑i,S.extraShift c i^2)=(∑i,S.shift i^2)+c^2 := by
  simp [extraShift,Fin.sum_univ_add]
end ReservedProgram

def sampleParent (E : Expression (Point d × Point d) d) (v : Fin E.slots → ℝ)
    (T η : ℝ) : ReservedProgram d where
  slots := 1+E.slots
  calls := E.calls
  pre := E.compile.seedMap (fun z : Point d × (Fin (1+E.slots) → Point d) =>
    ((z.1,z.2 (Fin.castAdd E.slots 0)),fun i => z.2 (Fin.natAdd 1 i))) (by fun_prop)
  shift := Fin.append (fun _ => -T) v
  reserve := η/2

lemma sampleParent_run (E : Expression (Point d × Point d) d) (v : Fin E.slots → ℝ)
    (T η : ℝ) (V : Point d → ℝ) (x : Point d) (g : Fin (1+E.slots) → Point d) :
    (sampleParent E v T η).pre.run V (x,g)=
      E.eval V (x,g (Fin.castAdd E.slots 0)) (fun i => g (Fin.natAdd 1 i)) := by
  change (E.compile.seedMap (fun z : Point d × (Fin (1+E.slots) → Point d) =>
    ((z.1,z.2 (Fin.castAdd E.slots 0)),fun i => z.2 (Fin.natAdd 1 i))) (by fun_prop)).run V (x,g)=_
  rw [Program.seedMap_run,Expression.compile_run]

def meanParent (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ) : SeedProgram d where
  slots := S.slots+(1+E.slots)
  calls := S.calls+E.calls
  program :=
    (S.program.seedMap (fun z : Point d × (Fin (S.slots+(1+E.slots)) → Point d) =>
      (z.1,leftBlock z.2)) (by unfold leftBlock; fun_prop)).seq
    (E.compile.seedMap (fun z =>
      ((z.1.1,(T • z.2,middleBlock z.1.2 0)),rightBlock z.1.2)) (by unfold middleBlock rightBlock; fun_prop))
  shift := Fin.append u (Fin.append (fun _ => 0) v)

lemma meanParent_run (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ)
    (V : Point d → ℝ) (x : Point d) (g : Fin (S.slots+(1+E.slots)) → Point d) :
    (meanParent S E u v T).program.run V (x,g)=
      E.eval V (x,(T • S.program.run V (x,leftBlock g),middleBlock g 0)) (rightBlock g) := by
  change ((S.program.seedMap _ _).seq (E.compile.seedMap _ _)).run V (x,g)=_
  rw [Program.seq_run,Program.seedMap_run,Program.seedMap_run,Expression.compile_run]

lemma meanParent_shift_energy (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ) :
    (∑i,(meanParent S E u v T).shift i^2)=(∑i,u i^2)+(∑i,v i^2) := by
  change (∑i : Fin (S.slots+(1+E.slots)), (Fin.append u (Fin.append (fun _ => 0) v)) i^2)=_
  simp [Fin.sum_univ_add]

lemma sampleParent_shift_energy (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (T η : ℝ) :
    (∑i,(sampleParent E v T η).shift i^2)=T^2+(∑i,v i^2) := by
  change (∑i : Fin (1+E.slots), (Fin.append (fun _ => -T) v) i^2)=_
  simp [Fin.sum_univ_add]

lemma mean_anchor_shift_identity {T R : ℝ} (hT : T≠0) (he : T^2+R^2=1)
    (y Δ : Point d) :
    T • (y-Δ+(R/(2*T)*(-2*R/T)) • Δ)=T • y-T⁻¹ • Δ := by
  have ha : T*(-1+R/(2*T)*(-2*R/T))=-T⁻¹ := by
    field_simp
    nlinarith
  simp only [smul_add,smul_sub,smul_smul]
  have hb : T*(R/(2*T)*(-2*R/T))-T=-T⁻¹ := by nlinarith [ha]
  calc
    _ = T • y+(T*(R/(2*T)*(-2*R/T))-T) • Δ := by module
    _ = _ := by rw [hb]; module
end LogConcaveSampling.OracleCompiler

end

end

end OAI
