import OAI.Analysis.AncientFlat.Evolution.FrozenAverage

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace ParametrixEvolution
open ParametrixVolterra FrozenParametrix
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}
lemma SourceEvolves.initial_derivative (hα : 0<α) (C L B : ℝ) (hC : 0≤C) (hL : 0≤L) (hB : 0≤B)
    (A : C(ℝ,V →ᵇ Icc α β)) (b : C(ℝ,V →ᵇ ℂ))
    (R : ℝ) (hR0 : 0<R) (hR : R≤1)
    (hb : ∀ s ∈ Icc 0 R, ‖b s‖≤B)
    (hLip : ∀ s ∈ Icc 0 R, ∀ r ∈ Icc 0 R, ∀ x z : V,
      |(A s x).val-(A r z).val|≤L*(‖x-z‖+|s-r|))
    (hLipb : ∀ s ∈ Icc 0 R, ∀ x z : V, ‖b s x-b s z‖≤L*‖x-z‖)
    (hA : ∀ s ∈ Icc 0 R, ContDiff ℝ ∞ (fun x => (A s x).val))
    (hAj : ∀ s ∈ Icc 0 R, ∀ n : ℕ, n≤2 → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (A s y).val) x‖≤C)
    (γ : ℝ) (hγ : 0<γ) (hγ1 : γ≤1) (f : ℝ →ᵇ C₀(V,ℂ))
    (hf : ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc 0 R, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ)
    (u : ℝ → C₀(V,ℂ)) (hu : SourceEvolves A b f 0 R 0 u) :
    Tendsto (fun t : ℝ => t⁻¹ • u t) (𝓝[>] 0) (𝓝 (f 0)) := by
  let : NormedAddCommGroup C₀(V,ℂ) := inferInstance
  let : NormedSpace ℝ C₀(V,ℂ) := inferInstance
  obtain ⟨E,hE,he⟩ := exists_zero_source_response hα L B hL hB A b R hR hb hLip hLipb hA γ hγ hγ1 f hf
  let I (t : ℝ) := ∫ r in (0:ℝ)..t, c0Time hα (A r) (t-r) (f r)
  have herr : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖t⁻¹ • (u t-I t)‖≤E*t^(1/4 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hR0)] with t ht htR
    obtain ⟨v,hv,hvb⟩ := he t ht htR.le
    have heq := (hu.end_mono htR.le).unique hv ht.le hα hC hB
      (fun s hs => hb s ⟨hs.1,hs.2.trans htR.le⟩)
      (fun s hs => (hA s ⟨hs.1,hs.2.trans htR.le⟩).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤)))
      (fun s hs => hAj s ⟨hs.1,hs.2.trans htR.le⟩) t ⟨ht.le,le_rfl⟩
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),heq]
    calc
      _≤t⁻¹*(E*t^(5/4 : ℝ)) := mul_le_mul_of_nonneg_left hvb (inv_nonneg.mpr ht.le)
      _=E*t^(1/4 : ℝ) := by
        rw [←Real.rpow_neg_one,show -(1:ℝ)=(-1:ℝ) by rfl]
        calc
          _=E*(t^(-1:ℝ)*t^(5/4 : ℝ)) := by ring
          _=_ := by rw [←Real.rpow_add ht]; norm_num
  have hz : Tendsto (fun t : ℝ => E*t^(1/4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hh := (Real.continuousAt_rpow_const 0 (1/4) (Or.inr (by norm_num))).tendsto.const_mul E
    simpa using hh.mono_left nhdsWithin_le_nhds
  have he0 := squeeze_zero_norm' herr hz
  have hh := he0.add (tendsto_frozen_average hα A f)
  simp only [zero_add] at hh
  apply hh.congr
  intro t
  change t⁻¹ • (u t-I t)+t⁻¹ • I t=t⁻¹ • u t
  rw [←smul_add,sub_add_cancel]
end ParametrixEvolution

end

end OAI
