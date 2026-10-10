import OAI.Dynamics.SmoothObstruction.ShortDerivative
import OAI.Dynamics.SmoothObstruction.ExteriorPowers

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.SmoothScales

/-- The source floor forces the gap×short-time scale to infinity. This is
`g L ≥ b^(3/4)n` for `g = sqrt b`, `L = ceil(b^(1/4)n)`. -/
lemma gap_scale_lower {b n : ℝ} (hn : 1≤n) (hb : n^(-1/10:ℝ)≤b) :
    n^(37/40:ℝ)≤b^(3/4:ℝ)*n := by
  have hnpos : 0<n := by linarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hb
    (show (0:ℝ)≤3/4 by norm_num)
  rw [←Real.rpow_mul hnpos.le] at hh
  calc
    n^(37/40:ℝ) = n^((-1/10:ℝ)*(3/4)+1) := by norm_num
    _ = n^((-1/10:ℝ)*(3/4))*n := by rw [Real.rpow_add hnpos,Real.rpow_one]
    _ ≤ b^(3/4:ℝ)*n := mul_le_mul_of_nonneg_right hh hnpos.le

/-- All fixed exponential gauge losses are absorbed by the genuine spectral
gap×short-time exponent. Neither the gap nor the rates need be bounded away
from zero. -/
theorem gap_cost_absorption {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (C : ℝ) {c : ℝ} (hc : 0<c) :
    Tendsto (fun k => Real.exp (C*b k*n k-c*b k^(3/4:ℝ)*n k)) l (𝓝 0) := by
  have hn1 : ∀ᶠ k in l,1≤n k := hn.eventually (eventually_ge_atTop 1)
  have hP : Tendsto (fun k => b k^(3/4:ℝ)*n k) l atTop := by
    apply tendsto_atTop_mono' l ?_
      ((tendsto_rpow_atTop (show (0:ℝ)<37/40 by norm_num)).comp hn)
    filter_upwards [hn1,hfloor] with k hnk hbk
    exact gap_scale_lower hnk hbk
  have hquarter : Tendsto (fun k => b k^(1/4:ℝ)) l (𝓝 0) := by
    have hh := ((Real.continuous_rpow_const (show (0:ℝ)≤1/4 by norm_num)).tendsto 0).comp hb
    simpa only [Function.comp_def,Real.zero_rpow (show (1/4:ℝ)≠0 by norm_num)] using hh
  have hs : ∀ᶠ k in l,C*b k^(1/4:ℝ)≤c/2 := by
    apply Tendsto.eventually_le_const (show (0:ℝ)<c/2 by linarith)
    simpa only [mul_zero] using hquarter.const_mul C
  have hzero := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hP.const_mul_atTop (show 0<c/2 by linarith))
  apply squeeze_zero' _ _ hzero
  · exact Filter.Eventually.of_forall fun k => (Real.exp_pos _).le
  · filter_upwards [hbpos,hn1,hs] with k hbk hnk hsk
    apply Real.exp_le_exp.mpr
    have hbseq : b k^(1/4:ℝ)*b k^(3/4:ℝ)=b k := by
      rw [←Real.rpow_add hbk]
      norm_num
    have hh := mul_le_mul_of_nonneg_right hsk
      (show 0≤b k^(3/4:ℝ)*n k from mul_nonneg (Real.rpow_nonneg hbk.le _) (by linarith))
    have he : (C*b k^(1/4:ℝ))*(b k^(3/4:ℝ)*n k)=C*b k*n k := by
      calc
        _ = C*(b k^(1/4:ℝ)*b k^(3/4:ℝ))*n k := by ring
        _ = _ := by rw [hbseq]
    rw [he] at hh
    nlinarith
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology
/-- Uniform exponentially small common-projector errors absorb every fixed
gauge cost. This is the form needed by the finite leading-minor lower bound. -/
theorem weighted_gap_error {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c A : ℝ} (hc : 0<c) (hA : 0≤A) (C : ℝ)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    Tendsto (fun k => A*Real.exp (C*b k*n k)*δ k) l (𝓝 0) := by
  have hz := (gap_cost_absorption hbpos hb hn hfloor C hc).const_mul A
  simp only [mul_zero] at hz
  apply squeeze_zero' _ _ hz
  · filter_upwards [hδ] with k hk
    exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) hk.1
  · filter_upwards [hδ] with k hk
    calc
      _ ≤ A*Real.exp (C*b k*n k)*Real.exp (-c*b k^(3/4:ℝ)*n k) :=
        mul_le_mul_of_nonneg_left hk.2 (mul_nonneg hA (Real.exp_pos _).le)
      _ = A*Real.exp (C*b k*n k-c*b k^(3/4:ℝ)*n k) := by
        rw [mul_assoc,←Real.exp_add]
        congr 2
        ring
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology

/-- The literal dimension/gauge cost in the common-fast leading-minor
proof is eventually small. Its parameters are fixed before bins and frames
are selected, and the good-frame error has the source gap×short-time scale. -/
theorem common_frame_budget {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c F C N : ℝ} (hc : 0<c) (hF : 0≤F) (hN : 0≤N)
    (K₀ : ℝ) (p : ℕ)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    ∀ᶠ k in l,
      (F*δ k)*(1+((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N)))≤1/2 := by
  have hz₁ := weighted_gap_error hbpos hb hn hfloor hc hF 0 hδ
  have hz₂ := weighted_gap_error hbpos hb hn hfloor hc
    (show 0≤F*C^6*2^p*N by positivity) ((4*p:ℕ)*K₀) hδ
  have hz := hz₁.add hz₂
  simp only [add_zero] at hz
  have he (k : α) :
      (F*δ k)*(1+((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N)))=
      F*Real.exp (0*b k*n k)*δ k+
        (F*C^6*2^p*N)*Real.exp (((4*p:ℕ):ℝ)*K₀*b k*n k)*δ k := by
    have hexp : Real.exp (((4*p:ℕ):ℝ)*K₀*b k*n k)=
        (Real.exp (K₀*b k*n k))^(4*p) := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    simp only [zero_mul,Real.exp_zero,mul_one,Nat.mul_comm 2 p,Nat.mul_comm 4 p,pow_mul]
    ring
  have hh : Tendsto (fun k =>
      (F*δ k)*(1+((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N)))) l (𝓝 0) := by
    apply hz.congr
    intro k
    exact (he k).symm
  exact hh.eventually_le_const (by norm_num : (0:ℝ)<1/2)
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology

/-- The full-time gap dominates the short-time gap scale and every fixed
gauge cost. No uniform positive lower bound on the spectral gap is assumed. -/
theorem weighted_full_gap {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c A : ℝ} (hc : 0<c) (hA : 0≤A) (C : ℝ) :
    Tendsto (fun k => A*Real.exp (C*b k*n k)*
      Real.exp (-c*b k^(1/2:ℝ)*n k)) l (𝓝 0) := by
  apply weighted_gap_error hbpos hb hn hfloor hc hA C
  have hb1 := hb.eventually_le_const (by norm_num : (0:ℝ)<1)
  have hn0 := hn.eventually (eventually_ge_atTop 0)
  filter_upwards [hbpos,hb1,hn0] with k hbk hb1k hnk
  refine ⟨(Real.exp_pos _).le,Real.exp_le_exp.mpr ?_⟩
  have hh := Real.rpow_le_rpow_of_exponent_ge hbk hb1k
    (show (1/2:ℝ)≤3/4 by norm_num)
  have hp := mul_le_mul_of_nonneg_right hh hnk
  nlinarith

/-- The literal finite-gauge Cramer bound tends to zero, uniformly over
all common bins satisfying the same scalar data. Fixed constants account
for the dimension, endpoint projections and unit wedge norms. -/
theorem common_graph_budget {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c C N V W : ℝ} (hc : 0<c) (hN : 0≤N)
    (hV : 0≤V) (hW : 0≤W) (K₀ : ℝ) (p : ℕ)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    Tendsto (fun k =>
      2*((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        ((C*(C*(Real.exp (K₀*b k*n k))^p)^2*N*V)*
            Real.exp (-2*b k^(1/2:ℝ)*n k)+
         (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N))*W*δ k)) l (𝓝 0) := by
  have hz₁ := weighted_full_gap hbpos hb hn hfloor
    (by norm_num : (0:ℝ)<2) (show 0≤2*C^6*2^p*N*V by positivity) ((4*p:ℕ)*K₀)
  have hz₂ := weighted_gap_error hbpos hb hn hfloor hc
    (show 0≤2*C^6*2^p*N*W by positivity) ((4*p:ℕ)*K₀) hδ
  have hz := hz₁.add hz₂
  simp only [add_zero] at hz
  apply hz.congr
  intro k
  have hexp : Real.exp (((4*p:ℕ):ℝ)*K₀*b k*n k)=
      (Real.exp (K₀*b k*n k))^(4*p) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  simp only [Nat.mul_comm 2 p,Nat.mul_comm 4 p,pow_mul]
  ring

/-- Relative nonlinear errors preserve the vanishing Cramer bound. -/
theorem perturbed_graph_decay {α : Type*} {l : Filter α} {θ ε : α → ℝ}
    (hθ : Tendsto θ l (𝓝 0)) (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (fun k => (θ k+ε k)/(1-ε k)) l (𝓝 0) := by
  have hh := (hθ.add hε).div (tendsto_const_nhds.sub hε)
    (by norm_num : (1:ℝ)-0≠0)
  change Tendsto (fun k => (θ k+ε k)/(1-ε k)) l (𝓝 ((0+0)/(1-0))) at hh
  norm_num at hh
  exact hh
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology

/-- The manuscript's exact natural short length, including its ceiling. -/
lemma ceil_gap_lower {b n : ℝ} (hb : 0<b) :
    b^(3/4:ℝ)*n≤Real.sqrt b*(Nat.ceil (b^(1/4:ℝ)*n):ℝ) := by
  calc
    _ = Real.sqrt b*(b^(1/4:ℝ)*n) := by
      rw [Real.sqrt_eq_rpow,←mul_assoc,←Real.rpow_add hb]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Real.sqrt_nonneg _)

lemma ceil_gap_error {b n c : ℝ} (hb : 0<b) (hc : 0≤c) :
    Real.exp (-c*Real.sqrt b*(Nat.ceil (b^(1/4:ℝ)*n):ℝ))≤
      Real.exp (-c*b^(3/4:ℝ)*n) := by
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (ceil_gap_lower (n:=n) hb) hc
  nlinarith

/-- Discharges the literal finite common-frame budget directly from the
source's `g = sqrt b` and `L = ceil(b^(1/4)n)`, without dropping the rounding
or imposing a positive gap floor. -/
theorem common_frame_budget_short {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    {c F C N : ℝ} (hc : 0<c) (hF : 0≤F) (hN : 0≤N) (K₀ : ℝ) (p : ℕ)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤
      Real.exp (-c*Real.sqrt (b k)*(Nat.ceil (b k^(1/4:ℝ)*n k):ℝ))) :
    ∀ᶠ k in l,
      (F*δ k)*(1+((C*(Real.exp (K₀*b k*n k))^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp (K₀*b k*n k))^(2*p)*N)))≤1/2 := by
  apply common_frame_budget hbpos hb hn hfloor hc hF hN K₀ p
  filter_upwards [hbpos,hδ] with k hbk hdk
  exact ⟨hdk.1,hdk.2.trans (ceil_gap_error hbk hc.le)⟩
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.SmoothScales
open Filter Topology

/-- Uniformity over every possible common-bin rank, including empty groups.
Constants may depend on the rank but are fixed before bins, points and times
are chosen. Thus no hidden point-dependent large-scale threshold remains. -/
theorem uniform_common_frame_budget {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) {c : ℝ} (hc : 0<c)
    (F C N K₀ : Fin (d+1) → ℝ) (hF : ∀ p,0≤F p) (hN : ∀ p,0≤N p)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤
      Real.exp (-c*Real.sqrt (b k)*(Nat.ceil (b k^(1/4:ℝ)*n k):ℝ))) :
    ∀ᶠ k in l,∀ p : Fin (d+1),
      (F p*δ k)*(1+((C p*(Real.exp (K₀ p*b k*n k))^p.val)^2*(C p*2^p.val))*
        (C p*((C p)^2*(Real.exp (K₀ p*b k*n k))^(2*p.val)*N p)))≤1/2 := by
  apply Filter.eventually_all.mpr
  intro p
  exact common_frame_budget_short hbpos hb hn hfloor hc (hF p) (hN p) (K₀ p) p.val hδ

/-- The actual Cramer error is small for all ranks simultaneously. Fixed
rank-dependent costs do not change the source's quantifier order. -/
theorem uniform_common_graph_budget {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) {c : ℝ} (hc : 0<c)
    (C N V W K₀ : Fin (d+1) → ℝ)
    (hN : ∀ p,0≤N p) (hV : ∀ p,0≤V p) (hW : ∀ p,0≤W p)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤
      Real.exp (-c*Real.sqrt (b k)*(Nat.ceil (b k^(1/4:ℝ)*n k):ℝ)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k in l,∀ p : Fin (d+1),
      2*((C p*(Real.exp (K₀ p*b k*n k))^p.val)^2*(C p*2^p.val))*
        ((C p*(C p*(Real.exp (K₀ p*b k*n k))^p.val)^2*N p*V p)*
            Real.exp (-2*b k^(1/2:ℝ)*n k)+
         (C p*((C p)^2*(Real.exp (K₀ p*b k*n k))^(2*p.val)*N p))*W p*δ k)≤ε := by
  apply Filter.eventually_all.mpr
  intro p
  apply (common_graph_budget hbpos hb hn hfloor hc (hN p) (hV p) (hW p)
    (K₀ p) p.val ?_).eventually_le_const hε
  filter_upwards [hbpos,hδ] with k hbk hdk
  exact ⟨hdk.1,hdk.2.trans (ceil_gap_error hbk hc.le)⟩
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.ExteriorStability

open RelativeProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Exterior powers commute with the source's time-ordered product. -/
theorem exterior_segment (p : ℕ) (A : ℕ → E →L[ℝ] E) (s n : ℕ) :
    exterior p (segment A s n) = segment (fun t => exterior p (A t)) s n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [segment_succ, exterior_mul, ih]

/-- Finite-product assertion of manuscript Lemma `lem:relative-exterior`,
in the canonical exterior Euclidean operator norm. The one-step constant
is uniform over all exterior degrees `p ≤ d`, all products and all lengths.
The proof actually does not need `a ≥ 0`, `m ≥ 1`, or `K ≥ 1`; the source
assumptions are retained in the final source-specialized statement. -/
theorem relative_exterior_core (d : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ), p ≤ d →
      ∀ (A B : ℕ → E →L[ℝ] E) (m : ℕ) (σ a ε : ℝ),
      0 ≤ ε → ε ≤ 1 →
      (∀ t < m, ‖A t‖ ≤ K) →
      (∀ t < m, ‖B t - A t‖ ≤ ε) →
      (∀ s k : ℕ, s + k ≤ m →
        ‖exterior p (segment A s k)‖ ≤ Real.exp (σ * k + a)) →
      ‖exterior p (segment B 0 m) - exterior p (segment A 0 m)‖ ≤
        Real.exp (σ * m + a) * ((1 + C * ε * Real.exp (a + |σ|)) ^ m - 1) := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_exterior_lipschitz (E := E) d K
  refine ⟨C, hCpos, ?_⟩
  intro p hp A B m σ a ε hε hε₁ hA hBA hseg
  simp only [exterior_segment]
  apply norm_difference_le_exp (fun t => exterior p (A t))
    (fun t => exterior p (B t)) 0 m σ a (C * ε) (mul_nonneg hCpos hε)
  · intro t k _ htk
    simpa only [← exterior_segment, Nat.zero_add] using hseg t k (by omega)
  · intro t _ ht
    exact (hC p hp (A t) (B t) (hA t (by omega)) ((hBA t (by omega)).trans hε₁)).trans
      (mul_le_mul_of_nonneg_left (hBA t (by omega)) hCpos)

/-- Exact finite estimate in `lem:relative-exterior` for real `d`-dimensional
Euclidean operators, hence real matrices in the Euclidean operator norm. -/
theorem relative_exterior (d : ℕ) (_hd : 1 ≤ d) (K : ℝ) (_hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ), p ≤ d →
      ∀ (m : ℕ), 1 ≤ m →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
        (σ a ε : ℝ),
      0 ≤ a → 0 ≤ ε → ε ≤ 1 →
      (∀ t < m, ‖A t‖ ≤ K) →
      (∀ t < m, ‖B t - A t‖ ≤ ε) →
      (∀ s k : ℕ, s + k ≤ m →
        ‖exterior p (segment A s k)‖ ≤ Real.exp (σ * k + a)) →
      ‖exterior p (segment B 0 m) - exterior p (segment A 0 m)‖ ≤
        Real.exp (σ * m + a) * ((1 + C * ε * Real.exp (a + |σ|)) ^ m - 1) := by
  obtain ⟨C, hC, hc⟩ := relative_exterior_core (E := EuclideanSpace ℝ (Fin d)) d K
  refine ⟨C, hC, fun p hp m _ A B σ a ε _ hε hε₁ hA hBA hseg => ?_⟩
  exact hc p hp A B m σ a ε hε hε₁ hA hBA hseg

end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.ExteriorStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
@[simp] theorem exterior_zero (A : E →L[ℝ] E) : exterior 0 A = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply (exteriorPower.zeroEquiv ℝ E).injective
  exact congrArg (fun f : (⋀[ℝ]^0 E) →ₗ[ℝ] ℝ => f v)
    (exteriorPower.zeroEquiv_naturality A.toLinearMap)
@[simp] theorem exterior_zero_difference (A B : E →L[ℝ] E) :
    exterior 0 B - exterior 0 A = 0 := by simp
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.SmoothScales
/-- The spatial exponent in the manuscript, with its literal positive root. -/
noncomputable def B (b : ℝ) : ℝ := b ^ (1 / 8 : ℝ)

lemma positive {b : ℝ} (hb : 0 < b) : 0 < B b := Real.rpow_pos_of_pos hb _

lemma ratio {b : ℝ} (hb : 0 < b) : b / B b = b ^ (7 / 8 : ℝ) := by
  calc
    b / B b = b ^ (1 : ℝ) / b ^ (1 / 8 : ℝ) := by simp [B]
    _ = b ^ ((1 : ℝ) - 1 / 8) := (Real.rpow_sub hb _ _).symm
    _ = b ^ (7 / 8 : ℝ) := by norm_num

lemma root_sixteen {b : ℝ} (hb : 0 ≤ b) : (B b)^16 = b^2 := by
  rw [B, ← Real.rpow_natCast, ← Real.rpow_mul hb]
  norm_num

lemma lower_bound {b n : ℝ} (hn : 1 ≤ n) (hb : n ^ (-1 / 10 : ℝ) ≤ b) :
    n ^ (79 / 80 : ℝ) ≤ B b * n := by
  have hnpos : 0 < n := by linarith
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hb (show (0 : ℝ) ≤ 1 / 8 by norm_num)
  rw [← Real.rpow_mul hnpos.le] at h
  have h' := mul_le_mul_of_nonneg_right h hnpos.le
  calc
    n ^ (79 / 80 : ℝ) = n ^ ((-1 / 10 : ℝ) * (1 / 8)) * n := by
      calc
        n ^ (79 / 80 : ℝ) = n ^ ((-1 / 10 : ℝ) * (1 / 8) + 1) := by norm_num
        _ = n ^ ((-1 / 10 : ℝ) * (1 / 8)) * n := by rw [Real.rpow_add hnpos, Real.rpow_one]
    _ ≤ B b * n := h'

lemma square_dominates {b n : ℝ} (hn : 1 ≤ n) (hb : n ^ (-1 / 10 : ℝ) ≤ b) :
    n ≤ (B b * n)^2 := by
  have hl := lower_bound hn hb
  have hpos : 0 ≤ n ^ (79 / 80 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc
    n = n ^ (1 : ℝ) := by simp
    _ ≤ n ^ ((79 / 80 : ℝ) * 2) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    _ = (n ^ (79 / 80 : ℝ))^2 := by rw [Real.rpow_mul (by linarith), Real.rpow_two]
    _ ≤ (B b * n)^2 := pow_le_pow_left₀ hpos hl 2

lemma ratio_tendsto_zero {α : Type*} {l : Filter α} {b : α → ℝ}
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0)) :
    Tendsto (fun k => b k / B (b k)) l (𝓝 0) := by
  have h := ((Real.continuous_rpow_const (show (0 : ℝ) ≤ 7 / 8 by norm_num)).tendsto 0).comp hb
  simp only [Real.zero_rpow (show (7 / 8 : ℝ) ≠ 0 by norm_num)] at h
  apply h.congr'
  filter_upwards [hbpos] with k hk
  exact (ratio hk).symm

/-- Quantitative exponential decay used in the relative-minor transfer. It
holds for every fixed real coefficient `C`, including all constants coming
from the dimension, charts, and inverse basis bounds. -/
theorem decisive_decay {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l, n k ^ (-1 / 10 : ℝ) ≤ b k) (C : ℝ) :
    Tendsto (fun k => n k * Real.exp (-(3 / 2 : ℝ) * B (b k) * n k + C * b k * n k))
      l (𝓝 0) := by
  have hn1 : ∀ᶠ k in l, 1 ≤ n k := hn.eventually (eventually_ge_atTop 1)
  have hsmall : ∀ᶠ k in l, C * (b k / B (b k)) ≤ 1 / 2 := by
    apply Tendsto.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num)
    simpa using (ratio_tendsto_zero hbpos hb).const_mul C
  have hBn : Tendsto (fun k => B (b k) * n k) l atTop := by
    apply tendsto_atTop_mono' l ?_ ((tendsto_rpow_atTop (show (0 : ℝ) < 79 / 80 by norm_num)).comp hn)
    filter_upwards [hn1, hfloor] with k hk hbf
    exact lower_bound hk hbf
  have hzero := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hBn
  apply squeeze_zero' _ _ hzero
  · filter_upwards [hn1] with k hk
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · filter_upwards [hn1, hfloor, hbpos, hsmall] with k hnk hfk hbk hsk
    have hB := positive hbk
    have hCB : C * b k ≤ B (b k) / 2 := by
      have hh := (div_le_iff₀ hB).mp (show C * b k / B (b k) ≤ 1 / 2 by simpa [mul_div_assoc] using hsk)
      linarith
    have hexp : -(3 / 2 : ℝ) * B (b k) * n k + C * b k * n k ≤ -(B (b k) * n k) := by
      have := mul_le_mul_of_nonneg_right hCB (show 0 ≤ n k by linarith)
      nlinarith
    exact mul_le_mul (square_dominates hnk hfk) (Real.exp_le_exp.mpr hexp)
      (Real.exp_pos _).le (sq_nonneg _)
end SmoothObstruction.SmoothScales

namespace SmoothObstruction.RelativeAsymptotics
lemma exp_sub_one_le (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith
lemma pow_one_add_sub_one_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (1 + x)^n - 1 ≤ n * x * Real.exp (n * x) := by
  have h : (1 + x)^n ≤ Real.exp (n * x) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    simpa [add_comm] using Real.add_one_le_exp x
  exact (sub_le_sub_right h 1).trans (exp_sub_one_le _)

lemma normalized_estimate (x σ a c C ε : ℝ) (m : ℕ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hx : x ≤ Real.exp (σ * m + a) * ((1 + C * ε * Real.exp (a + |σ|)) ^ m - 1)) :
    x / Real.exp (σ * m - c) ≤
      (C * m * ε * Real.exp (2 * a + c + |σ|)) *
        Real.exp (C * m * ε * Real.exp (a + |σ|)) := by
  have hnorm := mul_le_mul_of_nonneg_left
    (pow_one_add_sub_one_le (C * ε * Real.exp (a + |σ|)) (by positivity) m)
    (Real.exp_pos (σ * m + a)).le
  apply (div_le_div_of_nonneg_right (hx.trans hnorm) (Real.exp_pos _).le).trans
  apply le_of_eq
  have he : Real.exp (σ * m + a) = Real.exp (σ * m - c) * Real.exp (a + c) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  have he₂ : Real.exp (a + c) * Real.exp (a + |σ|) = Real.exp (2 * a + c + |σ|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he₃ : (m : ℝ) * (C * ε * Real.exp (a + |σ|)) = C * m * ε * Real.exp (a + |σ|) := by ring
  rw [he₃]
  field_simp
  ring_nf at he₂ ⊢
  rw [← he₂]
  ring

/-- The little-oh conclusion of the exterior-product lemma. The hypotheses on
`x` are the proved finite estimate, not an asymptotic conclusion. This bound
is uniform over all products and all exterior degrees covered by that estimate. -/
theorem uniform_relative_small {α : Type*} {l : Filter α}
    {b n x σ a ε : α → ℝ} {m : α → ℕ}
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l, n k ^ (-1 / 10 : ℝ) ≤ b k)
    (C C₀ C₁ C₂ C₃ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hC₃ : 0 ≤ C₃)
    (hdata : ∀ᶠ k in l,
      0 ≤ x k ∧ 0 ≤ a k ∧ 0 ≤ ε k ∧ (m k : ℝ) ≤ 2 * n k ∧
      a k ≤ C₁ * b k * n k ∧ |σ k| ≤ C₂ ∧
      ε k ≤ C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B (b k) * n k) ∧
      x k ≤ Real.exp (σ k * m k + a k) *
        ((1 + C * ε k * Real.exp (a k + |σ k|)) ^ m k - 1)) :
    Tendsto (fun k => x k / Real.exp (σ k * m k - C₀ * b k * n k)) l (𝓝 0) := by
  let U : α → ℝ := fun k => C * m k * ε k * Real.exp (a k + |σ k|)
  let D : α → ℝ := fun k => C * m k * ε k * Real.exp (2 * a k + C₀ * b k * n k + |σ k|)
  let V : α → ℝ := fun k => 2 * C * C₃ * Real.exp C₂ *
    (n k * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B (b k) * n k +
      (2 * C₁ + C₀) * b k * n k))
  have hn1 : ∀ᶠ k in l, 1 ≤ n k := hn.eventually (eventually_ge_atTop 1)
  have hV : Tendsto V l (𝓝 0) := by
    simpa [V] using (SmoothScales.decisive_decay hbpos hb hn hfloor (2 * C₁ + C₀)).const_mul
      (2 * C * C₃ * Real.exp C₂)
  have hDnonneg : ∀ᶠ k in l, 0 ≤ D k := by
    filter_upwards [hdata] with k hk
    dsimp [D]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hk.2.2.1) (Real.exp_pos _).le
  have hDle : ∀ᶠ k in l, D k ≤ V k := by
    filter_upwards [hdata, hn1] with k hk hnk
    rcases hk with ⟨_, _, hε, hm, ha, hσ, hεle, _⟩
    have hn0 : 0 ≤ n k := by linarith
    have hexp : 2 * a k + C₀ * b k * n k + |σ k| ≤
        (2 * C₁ + C₀) * b k * n k + C₂ := by nlinarith
    have hprod : C * m k * ε k ≤ C * (2 * n k) *
        (C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B (b k) * n k)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hm hC) hεle hε (by positivity)
    calc
      D k ≤ C * (2 * n k) * (C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B (b k) * n k)) *
          Real.exp ((2 * C₁ + C₀) * b k * n k + C₂) :=
        mul_le_mul hprod (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
      _ = V k := by
        dsimp [V]
        rw [Real.exp_add ((2 * C₁ + C₀) * b k * n k) C₂,
          Real.exp_add (-(3 / 2 : ℝ) * SmoothScales.B (b k) * n k)]
        ring
  have hD : Tendsto D l (𝓝 0) := squeeze_zero' hDnonneg hDle hV
  have hUnonneg : ∀ᶠ k in l, 0 ≤ U k := by
    filter_upwards [hdata] with k hk
    dsimp [U]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hk.2.2.1) (Real.exp_pos _).le
  have hUle : ∀ᶠ k in l, U k ≤ D k := by
    filter_upwards [hdata, hn1, hbpos] with k hk hnk hbk
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by
      exact mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) hk.2.2.1)
    have hbc : 0 ≤ C₀ * b k * n k := mul_nonneg (mul_nonneg hC₀ hbk.le) (by linarith)
    linarith [hk.2.1]
  have hU := squeeze_zero' hUnonneg hUle hD
  have hright : Tendsto (fun k => D k * Real.exp (U k)) l (𝓝 0) := by
    simpa using hD.mul (Real.continuous_exp.tendsto 0 |>.comp hU)
  apply squeeze_zero' _ _ hright
  · filter_upwards [hdata] with k hk
    exact div_nonneg hk.1 (Real.exp_pos _).le
  · filter_upwards [hdata] with k hk
    exact normalized_estimate (x k) (σ k) (a k) (C₀ * b k * n k) C (ε k) (m k) hC
      hk.2.2.1 hk.2.2.2.2.2.2.2
end SmoothObstruction.RelativeAsymptotics

namespace SmoothObstruction.RelativeAsymptotics
open Filter Topology

/-- A single, choice-independent numerical envelope for all the relative
exterior errors at a given dyadic scale. -/
noncomputable def envelope (C C₀ C₁ C₂ C₃ b n : ℝ) : ℝ :=
  2 * C * C₃ * Real.exp C₂ *
    (n * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n +
      (2 * C₁ + C₀) * b * n))

lemma uniform_relative_bound (x σ a ε b n C C₀ C₁ C₂ C₃ : ℝ) (m : ℕ)
    (hb : 0 ≤ b) (hn : 0 ≤ n) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hC₃ : 0 ≤ C₃)
    (ha0 : 0 ≤ a) (hε : 0 ≤ ε) (hm : (m : ℝ) ≤ 2 * n)
    (ha : a ≤ C₁ * b * n) (hσ : |σ| ≤ C₂)
    (hεle : ε ≤ C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n))
    (hx : x ≤ Real.exp (σ * m + a) *
      ((1 + C * ε * Real.exp (a + |σ|)) ^ m - 1)) :
    x / Real.exp (σ * m - C₀ * b * n) ≤
      envelope C C₀ C₁ C₂ C₃ b n * Real.exp (envelope C C₀ C₁ C₂ C₃ b n) := by
  let U := C * m * ε * Real.exp (a + |σ|)
  let D := C * m * ε * Real.exp (2 * a + C₀ * b * n + |σ|)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hUD : U ≤ D := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have : 0 ≤ C₀ * b * n := by positivity
    linarith
  have hDV : D ≤ envelope C C₀ C₁ C₂ C₃ b n := by
    have hexp : 2 * a + C₀ * b * n + |σ| ≤
        (2 * C₁ + C₀) * b * n + C₂ := by nlinarith
    have hprod : C * m * ε ≤ C * (2 * n) *
        (C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm hC) hεle hε (by positivity)
    calc
      D ≤ C * (2 * n) * (C₃ * Real.exp (-(3 / 2 : ℝ) * SmoothScales.B b * n)) *
          Real.exp ((2 * C₁ + C₀) * b * n + C₂) :=
        mul_le_mul hprod (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
      _ = _ := by
        dsimp [envelope]
        rw [Real.exp_add ((2 * C₁ + C₀) * b * n) C₂,
          Real.exp_add (-(3 / 2 : ℝ) * SmoothScales.B b * n)]
        ring
  exact (normalized_estimate x σ a (C₀*b*n) C ε m hC hε hx).trans
    (mul_le_mul hDV (Real.exp_le_exp.mpr (hUD.trans hDV)) (Real.exp_pos _).le (hD0.trans hDV))

lemma envelope_tendsto {α : Type*} {l : Filter α} {b n : α → ℝ}
    (hbpos : ∀ᶠ k in l, 0 < b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop)
    (hfloor : ∀ᶠ k in l, n k ^ (-1 / 10 : ℝ) ≤ b k)
    (C C₀ C₁ C₂ C₃ : ℝ) :
    Tendsto (fun k => envelope C C₀ C₁ C₂ C₃ (b k) (n k) *
      Real.exp (envelope C C₀ C₁ C₂ C₃ (b k) (n k))) l (𝓝 0) := by
  have hV : Tendsto (fun k => envelope C C₀ C₁ C₂ C₃ (b k) (n k)) l (𝓝 0) := by
    simpa [envelope] using
      (SmoothScales.decisive_decay hbpos hb hn hfloor (2 * C₁ + C₀)).const_mul
        (2 * C * C₃ * Real.exp C₂)
  simpa using hV.mul (Real.continuous_exp.tendsto 0 |>.comp hV)
end SmoothObstruction.RelativeAsymptotics

end

end OAI
