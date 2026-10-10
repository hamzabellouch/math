import OAI.Analysis.InterpolatedFactors.Scaling

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

namespace NormalTracialEquiv
variable {τA : A → ℂ} {τB : B → ℂ} {τC : C → ℂ}
variable {𝒯A : TopologicalSpace A} {𝒯B : TopologicalSpace B} {𝒯C : TopologicalSpace C}

def symm (e : NormalTracialEquiv τA τB 𝒯A 𝒯B) : NormalTracialEquiv τB τA 𝒯B 𝒯A where
  equiv := e.equiv.symm
  trace_eq x := by simpa only [StarAlgEquiv.apply_symm_apply] using (e.trace_eq (e.equiv.symm x)).symm
  normal := e.inverse_normal
  inverse_normal := e.normal

def trans (e : NormalTracialEquiv τA τB 𝒯A 𝒯B) (f : NormalTracialEquiv τB τC 𝒯B 𝒯C) :
    NormalTracialEquiv τA τC 𝒯A 𝒯C where
  equiv := e.equiv.trans f.equiv
  trace_eq x := (f.trace_eq (e.equiv x)).trans (e.trace_eq x)
  normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact f.normal.comp e.normal
  inverse_normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact e.inverse_normal.comp f.inverse_normal

end NormalTracialEquiv
end

open scoped ENNReal
variable {G : Type u_4} [Group G]

abbrev GroupCornerNormalIso (t : ℝ) (p : stabilization G) (hp : IsStarProjection p) :=
  NormalTracialEquiv (normalizedCornerTrace stabilizedTrace t p hp) canonicalTrace
    (cornerTopology (stabilizationTopology G) p hp) (groupUltraweakTopology G)

def unitNormalIso {A : Type u_5} [CStarAlgebra A] (τ : A → ℂ) (𝒯 : TopologicalSpace A) :
    NormalTracialEquiv (fun x : Corner (1:A) (IsStarProjection.one A) => τ x.val) τ
      (cornerTopology 𝒯 1 (IsStarProjection.one A)) 𝒯 where
  equiv := unitCornerEquiv.symm
  trace_eq _ := rfl
  normal := by
    let : TopologicalSpace A := 𝒯
    exact continuous_subtype_val
  inverse_normal := by
    let : TopologicalSpace A := 𝒯
    exact continuous_id.subtype_mk _

def finiteSingletonNormalIso (p : groupVonNeumann G) (hp : IsStarProjection p) :
    NormalTracialEquiv (normalizedCornerTrace stabilizedTrace 1 (finiteProjection 1 p)
      (finiteProjection_projection 1 p hp)) (fun x : Corner p hp => canonicalTrace x.val)
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 p) (finiteProjection_projection 1 p hp))
      (cornerTopology (groupUltraweakTopology G) p hp) where
  equiv := finiteCornerSingletonIso p hp
  trace_eq x := by
    simp only [normalizedCornerTrace,Complex.ofReal_one,inv_one,one_mul]
    exact finiteCornerSingletonIso_trace p hp x
  normal := finiteCornerSingletonIso_normal p hp
  inverse_normal := finiteCornerSingletonIso_symm_normal p hp

def finiteUnitCornerIso : GroupCornerNormalIso (G := G) 1
    (finiteProjection 1 (1 : groupVonNeumann G)) (finiteProjection_projection 1 1 (IsStarProjection.one _)) :=
  (finiteSingletonNormalIso (1 : groupVonNeumann G) (IsStarProjection.one _)).trans
    (unitNormalIso canonicalTrace (groupUltraweakTopology G))

theorem canonicalTrace_one : canonicalTrace (1 : groupVonNeumann G)=1 := by
  classical
  simp [canonicalTrace,lp.single_apply]

theorem finiteUnitProjection_trace :
    stabilizedProjectionTrace (finiteProjection 1 (1 : groupVonNeumann G))=ENNReal.ofReal 1 := by
  rw [finiteProjection_trace 1 1 (IsStarProjection.one _) 1 zero_le_one canonicalTrace_one]
  norm_num

theorem preferred_unit_iso
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (p : stabilization G) (hp : IsStarProjection p) (hptr : stabilizedProjectionTrace p=ENNReal.ofReal 1) :
    Nonempty (GroupCornerNormalIso 1 p hp) := by
  obtain ⟨e,heτ,hen,hein⟩ := finite_corner_choice_both (G := G) hbase 1 p
    (finiteProjection 1 (1 : groupVonNeumann G)) hp (finiteProjection_projection 1 1 (IsStarProjection.one _))
    (hptr.trans finiteUnitProjection_trace.symm) (hptr ▸ ENNReal.ofReal_ne_top)
  let E : NormalTracialEquiv (normalizedCornerTrace stabilizedTrace 1 p hp)
      (normalizedCornerTrace stabilizedTrace 1 (finiteProjection 1 (1 : groupVonNeumann G))
        (finiteProjection_projection 1 1 (IsStarProjection.one _)))
      (cornerTopology (stabilizationTopology G) p hp)
      (cornerTopology (stabilizationTopology G) (finiteProjection 1 (1 : groupVonNeumann G))
        (finiteProjection_projection 1 1 (IsStarProjection.one _))) := ⟨e,heτ,hen,hein⟩
  exact ⟨E.trans finiteUnitCornerIso⟩

theorem scaling_ratio_trace (t : ℝ) (ht : 0<t) (n : ℕ) (_hn : 0<(n:ℝ))
    (q r : groupVonNeumann G) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (f : groupVonNeumann G ≃⋆ₐ[ℂ] Corner q hq) (g : groupVonNeumann G ≃⋆ₐ[ℂ] Corner r hr)
    (hf : ∀ x,canonicalTrace (f x).val=((t/(n:ℝ):ℝ):ℂ)*canonicalTrace x)
    (hg : ∀ x,canonicalTrace (g x).val=((1/(n:ℝ):ℝ):ℂ)*canonicalTrace x)
    (x : Corner q hq) : canonicalTrace (g (f.symm x)).val=(t:ℂ)⁻¹*canonicalTrace x.val := by
  have hh := hf (f.symm x)
  rw [StarAlgEquiv.apply_symm_apply] at hh
  rw [hg,hh]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

 def finiteScaledIso (n : ℕ) (t : ℝ)
    (q r : groupVonNeumann G) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (e : Corner q hq ≃⋆ₐ[ℂ] Corner r hr)
    (heτ : ∀x,canonicalTrace (e x).val=(t:ℂ)⁻¹*canonicalTrace x.val)
    (hen : @Continuous _ _ (cornerTopology (groupUltraweakTopology G) q hq)
      (cornerTopology (groupUltraweakTopology G) r hr) e)
    (hein : @Continuous _ _ (cornerTopology (groupUltraweakTopology G) r hr)
      (cornerTopology (groupUltraweakTopology G) q hq) e.symm) :
    NormalTracialEquiv (normalizedCornerTrace stabilizedTrace t (finiteProjection n q) (finiteProjection_projection n q hq))
      (normalizedCornerTrace stabilizedTrace 1 (finiteProjection n r) (finiteProjection_projection n r hr))
      (cornerTopology (stabilizationTopology G) (finiteProjection n q) (finiteProjection_projection n q hq))
      (cornerTopology (stabilizationTopology G) (finiteProjection n r) (finiteProjection_projection n r hr)) where
  equiv := finiteCornerIso n q hq r hr e
  trace_eq x := by
    simp only [normalizedCornerTrace,Complex.ofReal_one,inv_one,one_mul]
    exact finiteCornerIso_trace n q hq r hr e (t:ℂ)⁻¹ heτ x
  normal := finiteCornerIso_normal n q hq r hr e hen
  inverse_normal := by
    rw [finiteCornerIso_symm]
    exact finiteCornerIso_normal n r hr q hq e.symm hein

end FreeGroupFactorMain.Amplification

end

end OAI
