import Mathlib
import OAI.Combinatorics.RamseyFive.Iteration.InitialPolar
import OAI.Combinatorics.RamseyFive.Iteration.PolarIteration
import OAI.Combinatorics.RamseyFive.Bounds.PrimeConstruction

namespace OAI

namespace SharpRamseyFive

section
open Module Filter FlagConstruction SelectedTuple Marking
open scoped Classical LinearAlgebra.Projectivization Topology
noncomputable section

theorem primeConstruction {η : ℝ} (hη : 0<η) (hη' : η<1/10) : PrimeConstruction η := by
  have hlog : Tendsto (fun q : ℕ=>Real.log (q:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent := hlog.eventually ((eventually_no_initial_polar hη hη' (1/2) 2 40
    (by norm_num) (by norm_num)).and (initial_floor_scales hη hη'))
  obtain ⟨q₀,hq₀⟩:=eventually_atTop.mp hevent
  refine ⟨max q₀ 3,?_⟩
  intro q hlarge hprime
  let : Fact q.Prime:=⟨hprime⟩
  let K:=ZMod q
  let V:=Space K
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K V)) := Module.finite_of_finite K
  let : Fintype (ℙ K V):=Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K V)):=Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K V))):=Fintype.ofFinite _
  let : Finite (Submodule K (Dual K V)):=Finite.of_injective
    (fun W : Submodule K (Dual K V)=>(W:Set (Dual K V))) SetLike.coe_injective
  let : Fintype (Submodule K (Dual K V)):=Fintype.ofFinite _
  have hd : finrank K V=5 := by simp [V,Space]
  let : Nonempty (RectangleGeometry.Flag (K:=K) (V:=V)):=
    Fintype.card_pos_iff.mp (RectangleGeometry.flags_nonempty hd)
  have hcard : Nat.card K=q := by simp [K,Nat.card_eq_fintype_card]
  let σ:=Real.log (q:ℝ)
  have hqp : (0:ℝ)<q := by exact_mod_cast hprime.pos
  have hqexp : Real.exp σ=Nat.card K := by rw [hcard];exact Real.exp_log hqp
  have hq3 : 3≤Nat.card K := by rw [hcard];exact (le_max_right _ _).trans hlarge
  obtain ⟨hforbid,hσ,hqexp3,hfloor,hlen⟩:=hq₀ q ((le_max_left _ _).trans hlarge)
  let N:=⌊(q:ℝ)^4*σ⌋₊
  let n:=⌊(q:ℝ)*σ^(1+η)⌋₊
  have heq : Real.exp σ=(q:ℝ) := Real.exp_log hqp
  change 1≤σ at hσ
  change ⌊Real.exp σ*σ^(1+η)⌋₊≤⌊(Real.exp σ)^4*σ⌋₊ at hfloor
  rw [heq] at hfloor
  have hN : (N:ℝ)≤(Nat.card K:ℝ)^4*σ := by
    rw [hcard]
    exact Nat.floor_le (by dsimp [σ];positivity)
  have hNexp : (N:ℝ)≤Real.exp (4*σ)*σ := by
    have he : Real.exp (4*σ)=(Nat.card K:ℝ)^4 := by
      simpa only [Nat.cast_ofNat,hqexp] using Real.exp_nat_mul σ 4
    rw [he]
    exact hN
  have hlen' : (1/2:ℝ)*(Nat.card K:ℝ)*σ^(1+η)≤(n:ℝ) := by
    simpa only [n,σ,Real.exp_log hqp,hcard] using hlen
  have hk : (n:ℝ)≤(Nat.card K:ℝ)*σ^(1+η) := by
    rw [hcard]
    exact Nat.floor_le (by positivity)
  by_contra hnone
  have hno : ∀s : Fin N→RectangleGeometry.Flag (K:=K) (V:=V),¬(graph s)ᶜ.CliqueFree n := by
    intro s hs
    exact hnone ⟨graph s,cliqueFree_five s,hs⟩
  obtain ⟨adm,⟨S⟩⟩:=initial_polar_of_no_graph (K:=K) hfloor σ hσ hqexp hq3 hN hno
  exact hforbid q K (RectangleGeometry.Flag (K:=K) (V:=V)) N n adm (40*σ) (n:ℝ) S
    hq3 hcard hσ hqexp (incidentFlag_log_card hd σ hqexp) hNexp hlen' le_rfl hk
    (by linarith only [hlen']) (by positivity) le_rfl
end
end

open Filter
open scoped Topology

theorem sharpExponent_of_sharpBounds (h : SharpBounds) : SharpExponent := by
  obtain ⟨C,hC,hb⟩ := h
  have ht : Tendsto (fun t : ℕ => (t:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp ht
  have hll := Real.tendsto_log_atTop.comp hl
  have hlog : ∀ᶠ t : ℕ in atTop, 0 < Real.log t ∧ 0 < Real.log (Real.log t) := by
    filter_upwards [hl.eventually (eventually_gt_atTop (1:ℝ))] with t hlt
    change 1 < Real.log (t:ℝ) at hlt
    exact ⟨by linarith,Real.log_pos hlt⟩
  have hnumeric (t : ℕ) (ε : ℝ) (ht : 2 ≤ t)
      (hlog : 0 < Real.log t) (hllog : 0 < Real.log (Real.log t))
      (hlo : (t:ℝ)^4 / Real.rpow (Real.log t) (3+ε) ≤ (ramsey 5 t:ℝ))
      (hhi : (ramsey 5 t:ℝ) ≤ C*(t:ℝ)^4/(Real.log t)^3) :
      3 - Real.log C / Real.log (Real.log t) ≤
        (4*Real.log t-Real.log (ramsey 5 t:ℝ))/Real.log (Real.log t) ∧
      (4*Real.log t-Real.log (ramsey 5 t:ℝ))/Real.log (Real.log t) ≤ 3+ε := by
    have htpos : 0 < (t:ℝ) := by exact_mod_cast (show 0<t by omega)
    have hp : 0 < (t:ℝ)^4 / Real.rpow (Real.log t) (3+ε) :=
      div_pos (pow_pos htpos _) (Real.rpow_pos_of_pos hlog _)
    have hrpos := hp.trans_le hlo
    have lower := Real.log_le_log hp hlo
    have upper := Real.log_le_log hrpos hhi
    rw [Real.log_div (x := (t:ℝ)^4) (y := Real.rpow (Real.log t) (3+ε)) (by positivity) (ne_of_gt (Real.rpow_pos_of_pos hlog _)),
      Real.log_pow,show Real.log (Real.rpow (Real.log t) (3+ε)) = (3+ε)*Real.log (Real.log t) from Real.log_rpow hlog (3+ε)] at lower
    rw [Real.log_div (by positivity) (by positivity),Real.log_mul (by positivity)
      (by positivity),Real.log_pow,Real.log_pow] at upper
    norm_num only [Nat.cast_ofNat] at lower upper
    constructor
    · apply (le_div_iff₀ hllog).mpr
      have heq : (3-Real.log C/Real.log (Real.log t))*Real.log (Real.log t) =
          3*Real.log (Real.log t)-Real.log C := by field_simp
      rw [heq]
      linarith
    · exact (div_le_iff₀ hllog).mpr (by linarith)
  unfold SharpExponent
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hconv : Tendsto (fun t : ℕ => 3-Real.log C/Real.log (Real.log t)) atTop (nhds 3) := by
      simpa using tendsto_const_nhds.sub ((tendsto_const_nhds (x := Real.log C)).div_atTop hll)
    obtain ⟨N,hN⟩ := hb 1 (by norm_num)
    filter_upwards [hconv.eventually (lt_mem_nhds ha),hlog,eventually_ge_atTop (max N 2)]
      with t hat hlt ht
    obtain ⟨hlo,hhi⟩ := hN t ((le_max_left _ _).trans ht)
    exact hat.trans_le (hnumeric t 1 ((le_max_right _ _).trans ht) hlt.1 hlt.2 hlo hhi).1
  · intro a ha
    let ε := (a-3)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨N,hN⟩ := hb ε hε
    filter_upwards [hlog,eventually_ge_atTop (max N 2)] with t hlt ht
    obtain ⟨hlo,hhi⟩ := hN t ((le_max_left _ _).trans ht)
    exact ((hnumeric t ε ((le_max_right _ _).trans ht) hlt.1 hlt.2 hlo hhi).2).trans_lt
      (by dsimp [ε]; linarith)

end SharpRamseyFive

end OAI
