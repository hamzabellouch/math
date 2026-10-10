import OAI.Analysis.CircleDomains.Selection.ExteriorDecay
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

/-!
# Classical normal-family inputs

The two propositions are classical consequences of Ahlfors,
*Complex Analysis*, third edition (1979):

* Chapter 5, Theorem 15, p. 224 (Montel compactness), in its diagonal
  exhaustion form, with the varying-domain convention of Chapter 5,
  Section 1.1, pp. 176–177. Holomorphy of the locally uniform limit
  follows from Mathlib.
* Chapter 5, Theorem 2, p. 178 (Hurwitz), applied to injective maps as in
  Chapter 6, Section 1.1, p. 231. Discarding finitely many initial terms
  gives the eventually holomorphic and injective formulation.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def MontelExhaustion : Prop :=
  ∀ (D : ℕ → Set ℂ) (F : ℕ → ℂ → ℂ),
    (∀ n, IsOpen (D n)) → Monotone D →
    (∀ n, DifferentiableOn ℂ (F n) (D n)) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
      ∃ M : ℝ, ∀ n z, z ∈ K → z ∈ D n → ‖F n z‖ ≤ M) →
    ∃ (s : ℕ → ℕ) (f : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n)

def HurwitzUnivalentLimit : Prop :=
  ∀ (D : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    IsOpen D → IsConnected D →
    (∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ InjOn (F n) D) →
    TendstoLocallyUniformlyOn F f atTop D →
    (¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) → InjOn f D

theorem holomorphic_limit_on_exhaustion
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n)) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n)) :
    DifferentiableOn ℂ f (⋃ n, D n) := by
  intro z hz
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  have hFm : ∀ᶠ n in atTop, DifferentiableOn ℂ (F (s n)) (D m) := by
    filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
    exact (hF (s n)).mono (hmono hn)
  have hf := (hlim.mono (subset_iUnion D m)).differentiableOn hFm (hD m)
  exact (hf.differentiableAt ((hD m).mem_nhds hm)).differentiableWithinAt

theorem univalent_limit_on_exhaustion
    (hhurwitz : HurwitzUnivalentLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {s : ℕ → ℕ} {f : ℂ → ℂ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n))
    (hmono : Monotone D) (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hFi : ∀ n, InjOn (F n) (D n)) (hs : StrictMono s)
    (hlim : TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop (⋃ n, D n))
    (hnonconst : ∀ n, ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c) :
    InjOn f (⋃ n, D n) := by
  have hfm (m : ℕ) : InjOn f (D m) := by
    apply hhurwitz (D m) (fun n => F (s n)) f (hD m) (hconn m)
    · filter_upwards [hs.tendsto_atTop.eventually_ge_atTop m] with n hn
      exact ⟨(hF (s n)).mono (hmono hn), (hFi (s n)).mono (hmono hn)⟩
    · exact hlim.mono (subset_iUnion D m)
    · exact hnonconst m
  intro z hz w hw heq
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  obtain ⟨n, hn⟩ := mem_iUnion.mp hw
  exact hfm (max m n) (hmono (le_max_left _ _) hm) (hmono (le_max_right _ _) hn) heq

end CircleDomainRigidity

end

end OAI
