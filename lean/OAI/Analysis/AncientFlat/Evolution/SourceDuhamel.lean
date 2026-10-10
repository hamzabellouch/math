import OAI.Analysis.AncientFlat.Evolution.MovingSource
import OAI.Analysis.AncientFlat.Evolution.TwistedDuhamel

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixEvolution ParametrixDilation
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def MovesWithSource (Af Bf : V → ℝ) (f : ℝ →ᵇ C₀(V,ℂ))
    (d : C₀(V,ℂ)) (u : ℝ → C₀(V,ℂ)) : Prop :=
  u 0=d ∧ ContinuousOn u (Icc (0:ℝ) 1) ∧
  (∀ t ∈ Ioo (0:ℝ) 1, ContDiff ℝ 4 (fun x => u t x)) ∧
  (∀ t ∈ Ioo (0:ℝ) 1, ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ n (fun y => u t y) x‖≤M) ∧
  (∀ t ∈ Ioo (0:ℝ) 1, ∃ p : V →ᵇ ℂ,
    HasDerivAt (fun r => (u r).toBCF) p t ∧ ∀ x,
    p x=f t (Real.exp (t/4) • x)-
      ((Real.exp (-t)/16*Af (Real.exp (t/4) • x) : ℝ) : ℂ)*
      Δ (Δ (fun y => u t y)) x-(1/2+(Bf (Real.exp (t/4) • x) : ℂ))*u t x)
theorem classical_duhamel (c : ℝ) (Af Bf : V → ℝ) (h : SymbolBounds c Af Bf)
    (S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)))
    (h0 : S 0=ContinuousLinearMap.id ℂ C₀(V,ℂ))
    (hc : ∀ d : C₀(V,ℂ), ContinuousOn (fun t => S t d) (Ici (0:ℝ)))
    (_ : ∃ K : ℝ, ∀ t ∈ Icc (0:ℝ) 1, ‖S t‖≤K)
    (ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s+t)=(S s).comp (S t))
    (hE : ∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), MovesClassically Af Bf d u ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S t d x=u t (Real.exp (-t/4) • x))
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x y,
      ‖f t x-f t y‖≤H*‖x-y‖^γ) (d : C₀(V,ℂ)) :
    ∃ u : ℝ → C₀(V,ℂ), MovesWithSource Af Bf f d u ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
        u t x=(S t d+∫ r in (0:ℝ)..t, S (t-r) (f r)) (Real.exp (t/4) • x) := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℂ C₀(V,ℂ) := inferInstance
  obtain ⟨α,β,C,L,B,hα,hC,hL,hB,A,b,hAe,hbe,hbound,hLip,hLipb,hA,hAj⟩ := h.moving_coefficients
  have hfg := movingSource_holder f γ hγ.le hf
  obtain ⟨u,hu⟩ := exists_source_evolves hα L B hL hB A b 1 zero_le_one le_rfl
    hbound hLip hLipb hA γ hγ hγ1 (movingSource f) hfg d
  have huc : MovesWithSource Af Bf f d u := by
    refine ⟨hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1,?_⟩
    intro t ht
    obtain ⟨p,hp,hpe⟩ := hu.2.2.2.2 t ht
    refine ⟨p,hp,fun x => ?_⟩
    rw [hpe x,movingSource_apply f ⟨ht.1.le,ht.2.le⟩,
      hAe t ⟨ht.1.le,ht.2.le⟩ x,hbe t ⟨ht.1.le,ht.2.le⟩ x]
  have hhom (e : C₀(V,ℂ)) : ∃ w : ℝ → C₀(V,ℂ), Evolves A b 0 1 e w ∧
      ∀ t ∈ Icc (0:ℝ) 1, S t e=dil t (w t) := by
    obtain ⟨w,hw,hwe⟩ := hE e
    refine ⟨w,⟨hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,?_⟩,?_⟩
    · intro t ht
      obtain ⟨p,hp,hpe⟩ := hw.2.2.2.2 t ht
      refine ⟨p,hp,fun x => ?_⟩
      rw [hAe t ⟨ht.1.le,ht.2.le⟩ x,hbe t ⟨ht.1.le,ht.2.le⟩ x]
      exact hpe x
    · intro t ht
      exact ZeroAtInftyContinuousMap.ext (hwe t ht)
  let v (t : ℝ) := dil t (u t)
  have hv : ContinuousOn v (Icc (0:ℝ) 1) := continuousOn_dil_apply hu.2.1
  have hd (s : ℝ) (hs : s ∈ Ico (0:ℝ) 1) :
      Tendsto (fun r : ℝ => (r-s)⁻¹ • (v r-S (r-s) (v s))) (𝓝[>] s) (𝓝 (f s)) := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.le⟩
    obtain ⟨w,hw,hwe⟩ := hhom (v s)
    let z (t : ℝ) := dil s (u (s+t))-w t
    have hR : 1-s≤1 := by linarith [hs.1]
    have hz : SourceEvolves A b (shiftedSource (movingSource f) s) 0 (1-s) 0 z := by
      have hh := (hu.dilate_shift Af (fun x => (Bf x : ℂ)) hAe hbe hs').sub
        (hw.end_mono hR).with_zero_source
      simpa only [shiftedSource,BoundedContinuousFunction.coe_ofNormedAddCommGroup,v,z,sub_zero,sub_self] using hh
    have hsub (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1-s)) : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans hR⟩
    have hz' := hz.initial_derivative hα C L B hC hL hB A b (1-s) (sub_pos.mpr hs.2) hR
      (fun t ht => hbound t (hsub t ht))
      (fun t ht r hr => hLip t (hsub t ht) r (hsub r hr))
      (fun t ht => hLipb t (hsub t ht))
      (fun t ht => hA t (hsub t ht))
      (fun t ht => hAj t (hsub t ht)) γ hγ hγ1 (shiftedSource (movingSource f) s)
      (shiftedSource_holder (movingSource f) γ hfg hs') z
    rw [shifted_movingSource_zero f hs'] at hz'
    have hz'' := tendsto_dil_apply (tendsto_id.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)) hz'
    simp only [dil_zero,ContinuousLinearMap.id_apply] at hz''
    have hshift : Tendsto (fun r : ℝ => r-s) (𝓝[>] s) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [id_eq,sub_self] using ((tendsto_id.sub_const s).mono_left
          (show 𝓝[>] s ≤ 𝓝 s from nhdsWithin_le_nhds))
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact sub_pos.mpr (show s<r from hr)
    have hh := hz''.comp hshift
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hs.2)] with r hr hr1
    change s<r at hr
    change r<1 at hr1
    have hrs : r-s ∈ Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hr.le,by linarith [hs.1,hr1]⟩
    dsimp only [Function.comp_apply]
    rw [ContinuousLinearMap.map_smul_of_tower]
    congr 1
    dsimp [z]
    rw [map_sub,←ContinuousLinearMap.comp_apply,←dil_add,
      sub_add_cancel,add_sub_cancel,←hwe (r-s) hrs]
  have hform (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      v t=S t d+∫ r in (0:ℝ)..t, S (t-r) (f r) := by
    have hh := AncientMild.duhamel_of_twisted_derivative S hc ha h0 v f f.continuous ht.1
      (hv.mono (Icc_subset_Icc_right ht.2)) (fun s hs => hd s ⟨hs.1,hs.2.trans_le ht.2⟩)
    have hv0 : v 0=d := by simp [v,hu.1]
    simpa only [hv0] using hh
  refine ⟨u,huc,fun t ht x => ?_⟩
  have hh := congrArg (fun a : C₀(V,ℂ) => a (Real.exp (t/4) • x)) (hform t ht)
  dsimp [v] at hh
  rw [smul_smul,←Real.exp_add,show -t/4+t/4=0 by ring,Real.exp_zero,one_smul] at hh
  simpa using hh
end FlatSimilarity

end

end OAI
