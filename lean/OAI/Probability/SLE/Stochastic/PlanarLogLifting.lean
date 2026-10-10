import OAI.Probability.SLE.Geometry.PublishedPlanarDiskOpenness
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

namespace OAI

/-! Elementary lifting facts used to prove the planar disk openness input.
An odd nonzero function on a connected antipodal space cannot have a
continuous logarithm. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma continuous_log_at_end_of_homotopy {A : Type*} [TopologicalSpace A]
    (H : C(unitInterval × A,ℂ)) (hH : ∀ q, H q≠0)
    (L : C(A,ℂ)) (hL : ∀ a, Complex.exp (L a)=H (0,a)) :
    ∃ M : C(A,ℂ), ∀ a, Complex.exp (M a)=H (1,a) := by
  let H' : C(unitInterval × A,{z : ℂ // z≠0}) :=
    ⟨fun q => ⟨H q,hH q⟩, H.continuous.subtype_mk _⟩
  have h0 (a : A) : H' (0,a)=⟨Complex.exp (L a),Complex.exp_ne_zero _⟩ :=
    Subtype.ext (hL a).symm
  let G := Complex.isCoveringMap_exp.liftHomotopy H' L h0
  refine ⟨G.comp ⟨fun a => (1,a),continuous_const.prodMk continuous_id⟩,fun a => ?_⟩
  have he := congr_fun (Complex.isCoveringMap_exp.liftHomotopy_lifts H' L h0) (1,a)
  exact congrArg Subtype.val he

lemma no_continuous_log_of_odd_involution {A : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] (J : A → A) (hJ : Continuous J) (hinv : Involutive J)
    (F L : C(A,ℂ)) (hne : ∀ a, F a≠0) (hodd : ∀ a, F (J a)= -F a)
    (hL : ∀ a, Complex.exp (L a)=F a) (a : A) : False := by
  let d : A → ℂ := fun x => L (J x)-L x
  have hd : Continuous d := (L.continuous.comp hJ).sub L.continuous
  have he (x : A) : Complex.exp (d x)= -1 := by
    simp only [d,Complex.exp_sub,hL,hodd]
    exact neg_div_self (hne x)
  have hconst (x y : A) : d x=d y :=
    Complex.isCoveringMap_exp.const_of_comp hd (by
      intro x y
      apply Subtype.ext
      exact (he x).trans (he y).symm) x y
  have hi : d (J a)= -d a := by simp only [d,hinv a]; ring
  have hz : d a=0 := by
    have heq := (hconst a (J a)).trans hi
    linear_combination (1/2:ℂ)*heq
  have := he a
  rw [hz,Complex.exp_zero] at this
  norm_num at this

end SLEExactGauge

end

end OAI
