import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralEndpointMultiplicity

namespace OAI

/-! A simple two-column determinant zero excludes a differentiated matching
chain. This is the finite boundary calculation needed for generalized modes. -/

namespace DefocusingNLS

theorem matchingColumn_no_chain (u v du dv : Fin 2 → ℂ) (hu : u≠0)
    (hz : matchingColumnDeterminant u v=0)
    (hd : matchingColumnDeterminant du v+matchingColumnDeterminant u dv≠0)
    (a b A B : ℂ) (hab : a≠0 ∨ b≠0)
    (he : a • u+b • v=0) : A • u+B • v+a • du+b • dv≠0 := by
  obtain ⟨c,hv⟩ := matchingColumnDeterminant_eq_zero_imp_smul u v hu hz
  have hc : a+b*c=0 := by
    apply (smul_eq_zero.mp ?_).resolve_right hu
    calc
      (a+b*c) • u = a • u+b • v := by rw [hv,smul_smul,add_smul]
      _ = 0 := he
  have hb : b≠0 := by
    intro hb
    have ha : a=0 := by simpa only [hb,zero_mul,add_zero] using hc
    exact hab.elim (fun h => h ha) (fun h => h hb)
  intro hchain
  have hd0 := congrArg (matchingColumnDeterminant u) hchain
  have hv0 := congrFun hv 0
  have hv1 := congrFun hv 1
  simp only [Pi.smul_apply,smul_eq_mul] at hv0 hv1
  simp only [matchingColumnDeterminant,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    Pi.zero_apply,hv0,hv1,mul_zero,sub_zero] at hd0
  have hprod : b*(matchingColumnDeterminant du v+matchingColumnDeterminant u dv)=0 := by
    simp only [matchingColumnDeterminant,hv0,hv1]
    linear_combination hd0-(u 0*du 1-u 1*du 0)*hc
  exact hd ((mul_eq_zero.mp hprod).resolve_left hb)

theorem matchingColumnDeterminant_hasDerivAt
    (U V : ℂ → Fin 2 → ℂ) (du dv : Fin 2 → ℂ) (z : ℂ)
    (hU : HasDerivAt U du z) (hV : HasDerivAt V dv z) :
    HasDerivAt (fun w => matchingColumnDeterminant (U w) (V w))
      (matchingColumnDeterminant du (V z)+matchingColumnDeterminant (U z) dv) z := by
  have hu0 := (hasDerivAt_pi.mp hU) 0
  have hu1 := (hasDerivAt_pi.mp hU) 1
  have hv0 := (hasDerivAt_pi.mp hV) 0
  have hv1 := (hasDerivAt_pi.mp hV) 1
  have he : matchingColumnDeterminant du (V z)+matchingColumnDeterminant (U z) dv =
      (du 0*V z 1+U z 0*dv 1)-(du 1*V z 0+U z 1*dv 0) := by
    simp only [matchingColumnDeterminant]
    ring
  rw [he]
  exact (hu0.mul hv1).sub (hu1.mul hv0)

theorem matchingColumn_simple_zero_no_chain
    (U V : ℂ → Fin 2 → ℂ) (z : ℂ)
    (hU : AnalyticAt ℂ U z) (hV : AnalyticAt ℂ V z) (hu : U z≠0)
    (hsimple : analyticOrderAt (fun w => matchingColumnDeterminant (U w) (V w)) z=1)
    (a b A B : ℂ) (hab : a≠0 ∨ b≠0) (he : a • U z+b • V z=0) :
    A • U z+B • V z+a • deriv U z+b • deriv V z≠0 := by
  let D := fun w => matchingColumnDeterminant (U w) (V w)
  have hD : AnalyticAt ℂ D z := analyticAt_matchingColumnDeterminant hU hV
  have hz : D z=0 := apply_eq_zero_of_analyticOrderAt_ne_zero
    (by rw [show analyticOrderAt D z=1 from hsimple]; exact one_ne_zero)
  have hdord : analyticOrderAt (deriv D) z=0 :=
    analyticOrderAt_deriv_of_pos hD (n := 0) (by simpa using hsimple)
  have hd : deriv D z≠0 := hD.deriv.analyticOrderAt_eq_zero.mp hdord
  have hder := matchingColumnDeterminant_hasDerivAt U V (deriv U z) (deriv V z) z
    hU.differentiableAt.hasDerivAt hV.differentiableAt.hasDerivAt
  rw [hder.deriv] at hd
  exact matchingColumn_no_chain (U z) (V z) (deriv U z) (deriv V z) hu hz hd a b A B hab he

end DefocusingNLS

end OAI
