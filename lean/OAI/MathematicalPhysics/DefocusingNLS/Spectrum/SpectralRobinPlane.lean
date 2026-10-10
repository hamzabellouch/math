import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalTrace

namespace OAI

/-! The Robin condition is precisely the two-column outgoing plane whenever
the value columns are invertible. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralTwoColumns_apply_inverse (u v z : ℂ × ℂ)
    (h : spectralValueDet u v ≠ 0) :
    spectralTwoColumns u v (spectralValueInverse u v z)=z := by
  rcases u with ⟨a,c⟩
  rcases v with ⟨b,d⟩
  rcases z with ⟨x,y⟩
  change a*d-c*b ≠ 0 at h
  apply Prod.ext
  · change ((a*d-c*b)⁻¹*(x*d+y*(-b)))*a+((a*d-c*b)⁻¹*(x*(-c)+y*a))*b=x
    field_simp [h]
    ring
  · change ((a*d-c*b)⁻¹*(x*d+y*(-b)))*c+((a*d-c*b)⁻¹*(x*(-c)+y*a))*d=y
    field_simp [h]
    ring

noncomputable def spectralJetRobin (U V : E₄) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  spectralRobinOperator (spectralPhysicalValueMap U) (spectralPhysicalValueMap V)
    (spectralPhysicalDerivativeMap U) (spectralPhysicalDerivativeMap V)

theorem spectralJetRobin_plane (U V W : E₄)
    (h : spectralValueDet (spectralPhysicalValueMap U) (spectralPhysicalValueMap V) ≠ 0) :
    spectralPhysicalDerivativeMap W=spectralJetRobin U V (spectralPhysicalValueMap W) ↔
      ∃ c : ℂ × ℂ, W=c.1 • U+c.2 • V := by
  constructor
  · intro hW
    let c := spectralValueInverse (spectralPhysicalValueMap U) (spectralPhysicalValueMap V)
      (spectralPhysicalValueMap W)
    have hv : spectralPhysicalValueMap (c.1 • U+c.2 • V)=spectralPhysicalValueMap W := by
      rw [map_add,map_smul,map_smul]
      exact spectralTwoColumns_apply_inverse _ _ _ h
    have hd : spectralPhysicalDerivativeMap (c.1 • U+c.2 • V)=spectralPhysicalDerivativeMap W := by
      rw [map_add,map_smul,map_smul,hW]
      rfl
    change ((c.1 • U+c.2 • V).1.1,(c.1 • U+c.2 • V).2.1)=(W.1.1,W.2.1) at hv
    change ((c.1 • U+c.2 • V).1.2,(c.1 • U+c.2 • V).2.2)=(W.1.2,W.2.2) at hd
    have h11 := congrArg (fun x : ℂ × ℂ => x.1) hv.symm
    have h12 := congrArg (fun x : ℂ × ℂ => x.1) hd.symm
    have h21 := congrArg (fun x : ℂ × ℂ => x.2) hv.symm
    have h22 := congrArg (fun x : ℂ × ℂ => x.2) hd.symm
    exact ⟨c,Prod.ext (Prod.ext h11 h12) (Prod.ext h21 h22)⟩
  · rintro ⟨c,rfl⟩
    change spectralPhysicalDerivativeMap (c.1 • U+c.2 • V)=
      spectralRobinOperator (spectralPhysicalValueMap U) (spectralPhysicalValueMap V)
        (spectralPhysicalDerivativeMap U) (spectralPhysicalDerivativeMap V)
        (spectralPhysicalValueMap (c.1 • U+c.2 • V))
    convert (spectralRobinOperator_columns (spectralPhysicalValueMap U)
      (spectralPhysicalValueMap V) (spectralPhysicalDerivativeMap U)
      (spectralPhysicalDerivativeMap V) c h).symm using 1 <;>
      simp only [spectralTwoColumns_apply,map_add,map_smul]

theorem spectralJetRobin_analyticAt (U V : ℂ → E₄) (z : ℂ)
    (hU : AnalyticAt ℂ U z) (hV : AnalyticAt ℂ V z)
    (h : spectralValueDet (spectralPhysicalValueMap (U z)) (spectralPhysicalValueMap (V z)) ≠ 0) :
    AnalyticAt ℂ (fun w => spectralJetRobin (U w) (V w)) z := by
  exact spectralRobinOperator_analyticAt _ _ _ _ z
    ((spectralPhysicalValueMap.analyticAt _).comp hU)
    ((spectralPhysicalValueMap.analyticAt _).comp hV)
    ((spectralPhysicalDerivativeMap.analyticAt _).comp hU)
    ((spectralPhysicalDerivativeMap.analyticAt _).comp hV) h

end DefocusingNLS

end OAI
