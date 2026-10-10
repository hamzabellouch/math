import OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowControl
open CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma height_product (v t H:ℝ)(hH:0≤H):
    1+‖v‖+‖t‖≤(1+‖v‖)*(1+|t|+H):=by
  simp only [Real.norm_eq_abs]
  nlinarith [abs_nonneg v,abs_nonneg t]

theorem reflected_child_control (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ))(degree:ℕ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t height:ℝ,0≤height →
      ((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2*
        (1+|t|+height)^degree≤
        D*(sourceControl T W)^2*(1+|t|+height)^(degree+2*n)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_profile_control a b ha hlo hhi S
  refine ⟨n,T,D^2,sq_pos_of_pos hD,?_⟩
  intro W hs j k v t height hheight
  have hbase:=hd W hs j k v t
  have hgrowth:(1+‖v‖+‖t‖)^n≤((1+‖v‖)*(1+|t|+height))^n:=
    pow_le_pow_left₀ (by positivity) (height_product v t height hheight) n
  have hprof:((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2≤
      (D*sourceControl T W*((1+‖v‖)*(1+|t|+height))^n)^2:=
    pow_le_pow_left₀ (Profiles.control_nonneg _ _) (hbase.trans
      (mul_le_mul_of_nonneg_left hgrowth (mul_nonneg hD.le (sourceControl_nonneg _ _)))) 2
  apply (mul_le_mul_of_nonneg_right hprof (by positivity)).trans_eq
  simp only [mul_pow] at *
  rw [pow_add,show (1+|t|+height)^(2*n)=((1+|t|+height)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul],
    show (1+‖v‖)^(2*n)=((1+‖v‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceLowControl

end

end OAI
