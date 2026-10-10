import OAI.MathematicalPhysics.Transonic.Shooting.Family
import OAI.MathematicalPhysics.Transonic.Shooting.EulerFamily
import OAI.MathematicalPhysics.Transonic.Shooting.RegularFamily
import OAI.MathematicalPhysics.Transonic.Shooting.EndpointSpecialization
import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyEulerSeed

namespace OAI

section
noncomputable section

namespace SepticProfile.SonicShooting
open Set SourceFamily RegularContinuation

theorem exists_family : Nonempty Family := by
  obtain ⟨G⟩ := SourceFamily.exists_uniform_germ
  obtain ⟨e,he,helt,her,hseed,hseedrange,hentry,hwhole⟩ := G.exists_uniform_euler_seed
  have heb : e≤5/6 := by linarith
  obtain ⟨u,huc,hu0,hud⟩ := EulerFamily.exists_family he heb _ hseed
  have hucont : Continuous (fun p => u p (5/6)) :=
    huc.comp (continuous_id.prodMk (continuous_const (y:=(⟨5/6,heb,le_rfl⟩:↥(Icc e (5/6))))))
  obtain ⟨v,hvc,hv0,hvd⟩ := RegularFamily.exists_family _ hucont
  have hb (p : Parameter) (hp : p ∈ ({leftParameter,rightParameter}:Set Parameter))
      (hc : SonicContinuation.PolynomialCertificate (sig p) (kap p) (slp p)) :
      u p (5/6) ∈ Icc
        ((EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction p)) (-1/1000)).eval (5/6))
        ((EulerPolynomial.barrier (SonicJet.jet (G.eulerFunction p)) (1/1000)).eval (5/6)) := by
    have hd := G.euler_jet_data p
    have hs : sig p<993/1000 := (ShootingParameters.sigma_shooting_bounds p.property).2
    apply EulerFamily.polynomial_trap
      (by linarith : sig p<1) he heb (hud p)
      _ _ (hc.lower_range _ hd.1 hd.2.1 hd.2.2)
      (hc.upper_range _ hd.1 hd.2.1 hd.2.2)
      (hc.lower_residual _ hd.1 hd.2.1 hd.2.2)
      (hc.upper_residual _ hd.1 hd.2.1 hd.2.2) ?_ (5/6) ⟨heb,le_rfl⟩
    rw [hu0]
    exact ⟨(hentry p hp).1.le,(hentry p hp).2.le⟩
  refine ⟨⟨G,e,he,helt,her,hwhole,u,v,huc,hvc,hu0,hv0,hud,hvd,?_,?_⟩⟩
  · have hdu := hvd leftParameter
    rw [sig_left_regular,kap_left_regular] at hdu
    apply RegularLowData.endpoint_bound hdu
    rw [hv0]
    exact ⟨G.left_entry_bounds.1.trans (hb leftParameter (by simp) left_certificate).1,
      (hb leftParameter (by simp) left_certificate).2.trans G.left_entry_bounds.2⟩
  · have hdu := hvd rightParameter
    rw [sig_right_regular,kap_right_regular] at hdu
    apply RegularHighData.endpoint_bound hdu
    rw [hv0]
    exact ⟨G.right_entry_bounds.1.trans (hb rightParameter (by simp) right_certificate).1,
      (hb rightParameter (by simp) right_certificate).2.trans G.right_entry_bounds.2⟩

end SepticProfile.SonicShooting

end
end

end OAI
