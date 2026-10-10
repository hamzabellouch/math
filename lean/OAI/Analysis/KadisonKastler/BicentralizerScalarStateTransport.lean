import OAI.Analysis.KadisonKastler.BicentralizerStateMembership
import OAI.Analysis.KadisonKastler.SpatialBicentralizer

namespace OAI

/-! # Scalar bicentralizers transfer between approximately conjugate states

One scalar bicentralizer suffices under the explicitly stated faithful
state homogeneity hypothesis. This does not prove that hypothesis.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vector_norm_sq_le_conjugate_state_distance (ξ η : H)
    (u : unitary (Algebra M)) (a : Algebra M) :
    ‖a.val ξ‖^2 ≤ ‖(u.val*a*star u.val).val η‖^2+
      ‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional η‖*‖a‖^2 := by
  let b : Algebra M := u.val*a*star u.val
  have hb : b*u.val=u.val*a := by
    dsimp only [b]
    rw [mul_assoc (u.val*a),u.property.1,mul_one]
  have hv : b.val (u.val.val ξ)=u.val.val (a.val ξ) :=
    congrArg (fun c : Algebra M => c.val ξ) hb
  have hn : ‖b‖=‖a‖ := by
    change ‖u.val*a*(star u).val‖=‖a‖
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  have hu : ‖u.val.val (a.val ξ)‖=‖a.val ξ‖ :=
    Unitary.norm_map (ambientAlgebraUnitary u) _
  have h := vector_norm_sq_le_state_distance η (u.val.val ξ) b
  rw [hv,hu,hn,← sandwichFunctional_vectorFunctional] at h
  exact h

theorem scalar_bicentralizer_of_comparing_unitaries (ξ η : H)
    (hξ : Function.Injective (algebraVectorMap M ξ))
    (hη : Function.Injective (algebraVectorMap M η))
    (u : ℕ → unitary (Algebra M))
    (hu : Tendsto (fun n =>
      ‖sandwichFunctional (vectorFunctional ξ) (u n).val-vectorFunctional η‖) atTop (𝓝 0))
    (hscalar : ∀ b : Algebra M, stateBicentralizerMember η b → ∃ z : ℂ, b=z • 1)
    (a : Algebra M) (ha : stateBicentralizerMember ξ a) : ∃ z : ℂ, a=z • 1 := by
  obtain ⟨b,_,hb⟩ := exists_bicentralizer_state_conjugate_limit ξ η hξ hη a ha u hu
  obtain ⟨z,hz⟩ := hscalar b
    (stateBicentralizerMember_of_state_conjugate_limit ξ η hη a b ha u hu hb)
  let d : Algebra M := a-z • 1
  have he (n : ℕ) : (u n).val*d*star (u n).val=
      (u n).val*a*star (u n).val-z • 1 := by
    let e := Unitary.conjStarAlgAut ℂ (Algebra M) (u n)
    change e (a-z • 1)=e a-z • 1
    rw [map_sub]
    have hs : e (z • (1 : Algebra M))=z • e 1 := e.map_smul' z 1
    rw [hs,map_one]
  have hd : Tendsto (fun n => ((u n).val*d*star (u n).val).val η) atTop (𝓝 0) := by
    have h := (hb η).sub_const ((z • (1 : Algebra M)).val η)
    rw [hz,sub_self] at h
    simpa only [he,AddSubgroupClass.coe_sub,sub_apply] using h
  have hlim : Tendsto (fun n =>
      ‖((u n).val*d*star (u n).val).val η‖^2+
      ‖sandwichFunctional (vectorFunctional ξ) (u n).val-vectorFunctional η‖*‖d‖^2)
      atTop (𝓝 0) := by
    simpa only [norm_zero,zero_pow (by decide : 2≠0),zero_mul,zero_add] using
      (hd.norm.pow 2).add (hu.mul_const (‖d‖^2))
  have hzero : Tendsto (fun _ : ℕ => ‖d.val ξ‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun n =>
      vector_norm_sq_le_conjugate_state_distance ξ η (u n) d) hlim
  have hzv : d.val ξ=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp
    (tendsto_nhds_unique tendsto_const_nhds hzero))
  have hd0 : d=0 := hξ (by
    change d.val ξ=(0 : H →L[ℂ] H) ξ
    simpa only [zero_apply] using hzv)
  exact ⟨z,sub_eq_zero.mp hd0⟩

theorem FaithfulVectorStateHomogeneity.scalar_bicentralizers_of_one
    (hhom : FaithfulVectorStateHomogeneity M) (η : H) (hnη : ‖η‖=1)
    (hη : Function.Injective (algebraVectorMap M η))
    (hscalar : ∀ b : Algebra M, stateBicentralizerMember η b → ∃ z : ℂ, b=z • 1) :
    FaithfulVectorBicentralizersScalar M := by
  intro ξ hnξ hξ a ha
  choose u hu using fun n : ℕ => hhom ξ η hnξ hnη hξ hη (1/((n : ℝ)+1)) (by positivity)
  have ht : Tendsto (fun n =>
      ‖sandwichFunctional (vectorFunctional ξ) (u n).val-vectorFunctional η‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact scalar_bicentralizer_of_comparing_unitaries ξ η hξ hη u ht hscalar a ha

end

end KadisonKastler

end OAI
