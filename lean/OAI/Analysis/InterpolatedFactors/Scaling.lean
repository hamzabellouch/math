import OAI.Analysis.InterpolatedFactors.WeightedCorner

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

def unitCornerEquiv : A ≃⋆ₐ[ℂ] Corner (1:A) (IsStarProjection.one A) where
  toFun a := ⟨a,⟨one_mul a,mul_one a⟩⟩
  invFun a := a.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

 theorem HasCornerScaling.one (τ : A → ℂ) (𝒯 : TopologicalSpace A) (hτ : τ 1=1) :
    HasCornerScaling τ 𝒯 1 := by
  refine ⟨1,(IsStarProjection.one A),unitCornerEquiv,?_,?_,?_,?_⟩
  · simpa only [Complex.ofReal_one] using hτ
  · let : TopologicalSpace A := 𝒯
    exact continuous_id.subtype_mk _
  · let : TopologicalSpace A := 𝒯
    exact continuous_subtype_val
  · intro x
    change τ x=(1:ℂ)*τ x
    rw [one_mul]

 theorem HasCornerScaling.pow (τ : A → ℂ) (𝒯 : TopologicalSpace A) (hτ : τ 1=1)
    {t : ℝ} (ht : HasCornerScaling τ 𝒯 t) (n : ℕ) : HasCornerScaling τ 𝒯 (t^n) := by
  induction n with
  | zero => simpa only [pow_zero] using HasCornerScaling.one τ 𝒯 hτ
  | succ n ih => simpa only [pow_succ] using ih.mul τ 𝒯 ht

 theorem HasCornerScaling.of_near_one (τ : A → ℂ) (𝒯 : TopologicalSpace A) (hτ : τ 1=1)
    (hnear : ∀ t : ℝ,1/2<t → t<1 → HasCornerScaling τ 𝒯 t)
    (t : ℝ) (ht : 0<t) (ht1 : t≤1) : HasCornerScaling τ 𝒯 t := by
  rcases lt_or_eq_of_le ht1 with ht1 | rfl
  swap
  · exact HasCornerScaling.one τ 𝒯 hτ
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1/2:ℝ)<1)
  have hn0 : n≠0 := by
    intro hn0
    rw [hn0,pow_zero] at hn
    exact (lt_irrefl (1:ℝ)) (hn.trans ht1)
  let r : ℝ := t^((n:ℝ)⁻¹)
  have hr0 : 0≤r := Real.rpow_nonneg ht.le _
  have hrpow : r^n=t := Real.rpow_inv_natCast_pow ht.le hn0
  have hrhalf : 1/2<r := by
    by_contra h
    have hh := pow_le_pow_left₀ hr0 (le_of_not_gt h) n
    rw [hrpow] at hh
    exact (not_le_of_gt hn) hh
  have hr1 : r<1 := Real.rpow_lt_one ht.le ht1 (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)))
  have h := HasCornerScaling.pow τ 𝒯 hτ (hnear r hrhalf hr1) n
  rwa [hrpow] at h

 theorem HasCornerScaling.transport (τA : A → ℂ) (τB : B → ℂ)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (e : A ≃⋆ₐ[ℂ] B) (hn : @Continuous _ _ 𝒯A 𝒯B e)
    (hin : @Continuous _ _ 𝒯B 𝒯A e.symm) (hτ : ∀x,τB (e x)=τA x)
    {t : ℝ} (ht : HasCornerScaling τA 𝒯A t) : HasCornerScaling τB 𝒯B t := by
  rcases ht with ⟨p,hp,f,hpτ,hfn,hfin,hfτ⟩
  let g := e.symm.trans (f.trans (cornerCongr e p hp))
  refine ⟨e p,map_projection e p hp,g,?_,?_,?_,?_⟩
  · rw [hτ,hpτ]
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    exact ((cornerCongr_normal e p hp 𝒯A 𝒯B hn).comp hfn).comp hin
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    let : TopologicalSpace (Corner (e p) (map_projection e p hp)) := cornerTopology 𝒯B (e p) (map_projection e p hp)
    exact hn.comp (hfin.comp (cornerCongr_symm_normal e p hp 𝒯A 𝒯B hin))
  · intro x
    change τB (e (f (e.symm x) : A))=(t:ℂ)*τB x
    rw [hτ,hfτ,←hτ,StarAlgEquiv.apply_symm_apply]
end

variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

 theorem HasCornerScaling.of_recognitions (τA : A → ℂ) (τB : B → ℂ)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (p : A) (hp : IsStarProjection p) (t : ℝ) (ht : t≠0) (hpt : τA p=(t:ℂ))
    (e : A ≃⋆ₐ[ℂ] B) (en : @Continuous _ _ 𝒯A 𝒯B e)
    (ein : @Continuous _ _ 𝒯B 𝒯A e.symm) (et : ∀x,τB (e x)=τA x)
    (f : Corner p hp ≃⋆ₐ[ℂ] B)
    (fn : @Continuous _ _ (cornerTopology 𝒯A p hp) 𝒯B f)
    (fin : @Continuous _ _ 𝒯B (cornerTopology 𝒯A p hp) f.symm)
    (ft : ∀x,τB (f x)=(t:ℂ)⁻¹*τA (x:A)) : HasCornerScaling τB 𝒯B t := by
  let g := f.symm.trans (cornerCongr e p hp)
  refine ⟨e p,map_projection e p hp,g,?_,?_,?_,?_⟩
  · rw [et,hpt]
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    exact (cornerCongr_normal e p hp 𝒯A 𝒯B en).comp fin
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    let : TopologicalSpace (Corner (e p) (map_projection e p hp)) :=
      cornerTopology 𝒯B (e p) (map_projection e p hp)
    exact fn.comp (cornerCongr_symm_normal e p hp 𝒯A 𝒯B ein)
  · intro x
    change τB (e (f.symm x : A))=(t:ℂ)*τB x
    rw [et,←StarAlgEquiv.apply_symm_apply f x,ft]
    rw [StarAlgEquiv.symm_apply_apply,←mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht),one_mul]
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition

local instance (G : Type u_5) [Group G] : IsClosed (groupVonNeumann G : Set (GroupOperator G)) :=
  Set.isClosed_centralizer _

 theorem scalar_hasCornerScaling_weighted (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (hunit : u^2+v^2=1) :
    HasCornerScaling scalarTrace (scalarSystem.generatedTopology scalarFlip) (u^2) := by
  have hu : u≠0 := (lt_trans hv hvu).ne'
  have hv' : v≠0 := hv.ne'
  apply HasCornerScaling.of_recognitions (fun T : ambientAlgebra (ι := ℕ) u v => vacuumTrace u v (T : WeightedFock.Operator ℕ))
    scalarTrace (ambientTopology u v) (scalarSystem.generatedTopology scalarFlip)
    (ambientP u v) (ambientP_projection u v) (u^2) (pow_ne_zero 2 hu)
    (vacuumTrace_P u v) (ambientScalarIso u v hu hv' hunit)
    (ambientScalarIso_normal u v hu hv' hunit) (ambientScalarIso_symm_normal u v hu hv' hunit)
    (ambientScalarIso_trace u v hu hv' hunit) (ambientCornerGaussianIso u v hv hvu)
    (ambientCornerGaussianIso_normal u v hv hvu) (ambientCornerGaussianIso_symm_normal u v hv hvu)
  intro x
  change inner ℂ scalarSystem.root
    ((ambientCornerGaussianIso u v hv hvu x : FreeFock.Operator ScalarIndex) scalarSystem.root)=_
  rw [ambientCornerGaussianIso_trace,pVacuumTrace,Complex.ofReal_pow,←inv_pow]
  ring

 theorem scalar_hasCornerScaling_near_one (t : ℝ) (ht : 1/2<t) (ht1 : t<1) :
    HasCornerScaling scalarTrace (scalarSystem.generatedTopology scalarFlip) t := by
  have ht0 : 0<t := by linarith
  have hs0 : 0<1-t := sub_pos.mpr ht1
  have hv : 0<Real.sqrt (1-t) := Real.sqrt_pos.mpr hs0
  have hvu : Real.sqrt (1-t)<Real.sqrt t := Real.sqrt_lt_sqrt hs0.le (by linarith)
  have ht2 := Real.sq_sqrt ht0.le
  have hs2 := Real.sq_sqrt hs0.le
  have hunit : (Real.sqrt t)^2+(Real.sqrt (1-t))^2=1 := by rw [ht2,hs2]; ring
  have hh := scalar_hasCornerScaling_weighted (Real.sqrt t) (Real.sqrt (1-t)) hv hvu hunit
  rwa [ht2] at hh

 theorem scalarTrace_one : scalarTrace 1=1 := by
  exact FreeFock.vacuumTrace_one

 theorem scalar_hasCornerScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling scalarTrace (scalarSystem.generatedTopology scalarFlip) t :=
  HasCornerScaling.of_near_one scalarTrace (scalarSystem.generatedTopology scalarFlip)
    scalarTrace_one scalar_hasCornerScaling_near_one t ht ht1

 theorem scalarGroup_hasCornerScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling (canonicalTrace (G := FreeGroup ScalarIndex))
      (groupUltraweakTopology (FreeGroup ScalarIndex)) t := by
  apply HasCornerScaling.transport scalarTrace canonicalTrace
    (scalarSystem.generatedTopology scalarFlip) (groupUltraweakTopology (FreeGroup ScalarIndex))
    scalarGroupIso.symm scalarGroupIso_symm_normal scalarGroupIso_normal
    (fun T => ?_) (scalar_hasCornerScaling t ht ht1)
  simpa only [StarAlgEquiv.apply_symm_apply] using (scalarGroupIso_trace (scalarGroupIso.symm T)).symm
end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
open WeightedFock FreeFock

theorem smallScaling_transport_group {G : Type u_6} {H : Type u_7} [Group G] [Group H]
    (h : HasNormalTracialIso G H) {t : ℝ}
    (ht : HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t) :
    HasCornerScaling (canonicalTrace (G := H)) (groupUltraweakTopology H) t := by
  classical
  obtain ⟨Φ,hΦ,_⟩ := h
  obtain ⟨e,hδ,he⟩ := spatial_of_trace_iso Φ hΦ
  apply HasCornerScaling.transport canonicalTrace canonicalTrace
    (groupUltraweakTopology G) (groupUltraweakTopology H)
    (spatialGroupIso e he) (spatialGroupIso_normal e he) (spatialGroupIso_symm_normal e he) ?_ ht
  intro T
  rw [canonicalTrace_eq_inner,canonicalTrace_eq_inner]
  change inner ℂ deltaOne (e ((T : GroupOperator G) (e.symm deltaOne)))=_
  rw [←hδ,e.symm_apply_apply,e.inner_map_map]

theorem infinite_hasCornerScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling (canonicalTrace (G := FreeGroup ℕ))
      (groupUltraweakTopology (FreeGroup ℕ)) t := by
  classical
  let : Denumerable ScalarIndex := Denumerable.ofEncodableOfInfinite ScalarIndex
  let e : ScalarIndex ≃ ℕ := (Denumerable.eqv ScalarIndex)
  exact smallScaling_transport_group (normalTracialIso_of_groupEquiv (FreeGroup.freeGroupCongr e))
    (scalarGroup_hasCornerScaling t ht ht1)
end FreeGroupFactorMain.Amplification

end

end OAI
