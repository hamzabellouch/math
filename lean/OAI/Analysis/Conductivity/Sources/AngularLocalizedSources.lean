import Mathlib
import OAI.Analysis.Conductivity.Fourier.AngularPeriodization
import OAI.Analysis.Conductivity.Fourier.SmoothAngularCutoff

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

def angularCutoff (T : ℝ) (x : Coord3) : ℝ := periodCutoff T (x 1)*periodCutoff T (x 2)

lemma angularCutoff_smooth (T : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (angularCutoff T) :=
  ((periodCutoff_smooth T).comp (by fun_prop)).mul
    ((periodCutoff_smooth T).comp (by fun_prop))

lemma angularCutoff_support {T : ℝ} (hT : 0<T) :
    tsupport (angularCutoff T)⊆{x | x 1∈Icc (-T) T ∧ x 2∈Icc (-T) T} := by
  apply closure_minimal _ ((isClosed_Icc.preimage (continuous_apply 1)).inter
    (isClosed_Icc.preimage (continuous_apply 2)))
  intro x hx
  have ha : periodCutoff T (x 1)≠0 := fun h => hx (by simp [angularCutoff,h])
  have hb : periodCutoff T (x 2)≠0 := fun h => hx (by simp [angularCutoff,h])
  exact ⟨periodCutoff_support hT (subset_tsupport _ ha),periodCutoff_support hT (subset_tsupport _ hb)⟩

lemma angularCutoff_finsum {T : ℝ} (hT : 0<T) (x : Coord3) :
    (∑ᶠ n : Fin 2 → ℤ,angularCutoff T (x+angularShift T n))=1 := by
  let a : ℤ → ℝ := fun n => periodCutoff T (x 1+T*n)
  let b : ℤ → ℝ := fun n => periodCutoff T (x 2+T*n)
  have ha : (∑ᶠ n,a n)=1 := periodCutoff_finsum hT _
  have hb : (∑ᶠ n,b n)=1 := periodCutoff_finsum hT _
  have hf : Function.HasFiniteSupport (fun z : ℤ×ℤ => a z.1*b z.2) := by
    apply ((hasFiniteSupport_of_finsum_eq_one ha).prod (hasFiniteSupport_of_finsum_eq_one hb)).subset
    intro z hz
    exact ⟨fun h => hz (by simp [h]),fun h => hz (by simp [h])⟩
  change (∑ᶠ n : Fin 2 → ℤ,a (n 0)*b (n 1))=1
  have he := finsum_comp_equiv (MeasurableEquiv.finTwoArrow (α:=ℤ)).symm.toEquiv
    (f:=fun n : Fin 2 → ℤ => a (n 0)*b (n 1))
  change (∑ᶠ z : ℤ×ℤ,a z.1*b z.2)=(∑ᶠ n : Fin 2 → ℤ,a (n 0)*b (n 1)) at he
  rw [←he,finsum_curry _ hf]
  simp_rw [←mul_finsum,hb,mul_one]
  exact ha

lemma angularCutoff_periodize {T : ℝ} (hT : 0<T) {f : Coord3 → ℝ} (hp : AngularPeriodic T f) :
    angularPeriodize T (fun x => angularCutoff T x*f x)=f := by
  funext x
  unfold angularPeriodize
  have he : (fun n : Fin 2 → ℤ => angularCutoff T (x+angularShift T n)*f (x+angularShift T n))=
      (fun n => angularCutoff T (x+angularShift T n)*f x) := by
    funext n; rw [hp n x]
  rw [he]
  rw [←finsum_mul,angularCutoff_finsum hT,one_mul]

lemma angularCutoff_compact_support {T a b : ℝ} (hT : 0<T) {f : Coord3 → ℝ}
    (hf : tsupport f⊆{x | x 0∈Icc a b}) :
    tsupport (fun x => angularCutoff T x*f x)⊆Icc ![a,-T,-T] ![b,T,T] := by
  intro x hx
  have h0 := hf ((tsupport_mul_subset_right (f:=angularCutoff T) (g:=f)) hx)
  have hθ := angularCutoff_support hT ((tsupport_mul_subset_left (f:=angularCutoff T) (g:=f)) hx)
  constructor <;> intro i <;> fin_cases i
  · exact h0.1
  · exact hθ.1.1
  · exact hθ.2.1
  · exact h0.2
  · exact hθ.1.2
  · exact hθ.2.2

lemma angularCutoff_compact {T a b : ℝ} (hT : 0<T) {f : Coord3 → ℝ}
    (hf : tsupport f⊆{x | x 0∈Icc a b}) :
    HasCompactSupport (fun x => angularCutoff T x*f x) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (angularCutoff_compact_support hT hf)

lemma AngularPeriodic.coordinate_one {T : ℝ} {f : Coord3 → ℝ} (hp : AngularPeriodic T f)
    (t z : ℝ) : Function.Periodic (fun y => f ![t,y,z]) T := by
  intro y
  have hh := hp ![1,0] ![t,y,z]
  have he : ![t,y,z]+angularShift T ![1,0]=![t,y+T,z] := by
    ext i; fin_cases i <;> simp [angularShift]
  rw [he] at hh
  exact hh

lemma AngularPeriodic.coordinate_two {T : ℝ} {f : Coord3 → ℝ} (hp : AngularPeriodic T f)
    (t y : ℝ) : Function.Periodic (fun z => f ![t,y,z]) T := by
  intro z
  have hh := hp ![0,1] ![t,y,z]
  have he : ![t,y,z]+angularShift T ![0,1]=![t,y,z+T] := by
    ext i; fin_cases i <;> simp [angularShift]
  rw [he] at hh
  exact hh

end ScalarConductivity

end
end

end OAI
