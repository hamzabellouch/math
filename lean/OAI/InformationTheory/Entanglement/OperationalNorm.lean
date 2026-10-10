import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SecretKey

theorem recovered_gap_limit {E : Type*} [SeminormedAddCommGroup E]
    {D : ℕ → Type*} [∀ k, SeminormedAddCommGroup (D k)]
    (τ : ℕ → E) (τlim γ : E) (original : (k : ℕ) → D k)
    (recover : (k : ℕ) → E → D k)
    (hrec : ∀ k, recover k (τ k)=original k)
    (hcontract : ∀ k x y, ‖recover k x-recover k y‖≤‖x-y‖)
    (hgap : ∀ k, 1/5≤‖original k-recover k γ‖)
    (hlim : Tendsto τ atTop (𝓝 τlim)) : 1/5≤‖τlim-γ‖ := by
  have ht : Tendsto (fun k => ‖τ k-γ‖) atTop (𝓝 ‖τlim-γ‖) :=
    (hlim.sub tendsto_const_nhds).norm
  apply ge_of_tendsto ht
  exact Filter.Eventually.of_forall fun k => (hgap k).trans (by simpa only [hrec] using hcontract k (τ k) γ)

theorem abort_replacement_bound {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : ℝ) (hδ0 : 0≤δ) (hδ1 : δ≤1) (ok bad γ : E)
    (hstates : ‖bad-γ‖≤2) :
    ‖((1-δ) • ok+δ • bad)-γ‖≤(1-δ)*‖ok-γ‖+2*δ := by
  have he : ((1-δ) • ok+δ • bad)-γ=(1-δ) • (ok-γ)+δ • (bad-γ) := by
    module
  rw [he]
  calc
    _≤‖(1-δ) • (ok-γ)‖+‖δ • (bad-γ)‖ := norm_add_le _ _
    _=(1-δ)*‖ok-γ‖+δ*‖bad-γ‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hδ1),abs_of_nonneg hδ0]
    _≤(1-δ)*‖ok-γ‖+2*δ := by nlinarith

theorem vanishing_abort_contradicts_gap (δ error replaced : ℕ → ℝ)
    (hδ0 : ∀ k, 0≤δ k) (hδ1 : ∀ k, δ k≤1) (he0 : ∀ k, 0≤error k)
    (hbound : ∀ k, replaced k≤(1-δ k)*error k+2*δ k)
    (hgap : ∀ k, 1/5≤replaced k)
    (hδ : Tendsto δ atTop (𝓝 0)) (he : Tendsto error atTop (𝓝 0)) : False := by
  have herror : Tendsto (fun k => (1-δ k)*error k) atTop (𝓝 0) :=
    squeeze_zero
      (fun k => mul_nonneg (sub_nonneg.mpr (hδ1 k)) (he0 k))
      (fun k => mul_le_of_le_one_left (he0 k) (sub_le_self _ (hδ0 k))) he
  have ht : Tendsto (fun k => (1-δ k)*error k+2*δ k) atTop (𝓝 0) := by
    simpa using herror.add (hδ.const_mul 2)
  have hh : (1:ℝ)/5≤0 := ge_of_tendsto ht
    (Filter.Eventually.of_forall fun k => (hgap k).trans (hbound k))
  norm_num at hh

end SecretKey

end

end OAI
