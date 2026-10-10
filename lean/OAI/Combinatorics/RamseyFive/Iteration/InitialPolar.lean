import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.FlagGraph

namespace OAI

namespace SharpRamseyFive

namespace FlagConstruction
open Module ProjectiveIncidence FiniteEntropy SelectedTuple CoreGeometry Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K : Type} [Field K] [Finite K]
  [Fintype (Point K)] [Fintype (DualPoint K)]
  [Fintype (ℙ K (Dual K (Dual K (Space K))))]
  [Fintype (Submodule K (Dual K (Space K)))]
  [Nonempty (RectangleGeometry.Flag (K:=K) (V:=Space K))] [Nonempty (Point K)] [Nonempty (DualPoint K)]
  [Nonempty (ℙ K (Dual K (Dual K (Space K))))]

omit [Finite K] [Fintype (ℙ K (Dual K (Dual K (Space K))))]
  [Fintype (Submodule K (Dual K (Space K)))]
  [Nonempty (RectangleGeometry.Flag (K:=K) (V:=Space K))]
  [Nonempty (Point K)] [Nonempty (DualPoint K)]
  [Nonempty (ℙ K (Dual K (Dual K (Space K))))] in
lemma rectangle_mem_iff (U : Submodule K (Dual K (Space K))) (x : RectangleGeometry.Flag (K:=K) (V:=Space K)) :
    x∈RectangleGeometry.rectangle U ↔ InRectangle U x.val.1.rep x.val.2.rep := by
  simp [RectangleGeometry.rectangle,InRectangle,rep_mem_iff]

theorem initial_polar_of_no_graph {N n : ℕ} (hn : n≤N) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hq3 : 3≤Nat.card K)
    (hN : (N:ℝ)≤(Nat.card K:ℝ)^4*σ)
    (hno : ∀s : Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K),¬(graph s)ᶜ.CliqueFree n) :
    ∃ adm : (Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K))→Prop,
      Nonempty (PolarState K (RectangleGeometry.Flag (K:=K) (V:=Space K)) N n adm 2 0 (10*σ) (40*σ)) := by
  let : Nonempty (Flag K) := ‹Nonempty (RectangleGeometry.Flag (K:=K) (V:=Space K))›
  have hd : finrank K (Space K)=5 := by simp [Space]
  have hs : 0≤σ := by linarith
  have hqp : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hlog : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  let bad : Finset (Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)) := Finset.univ.biUnion fun U : Submodule K (Dual K (Space K)) =>
    Finset.univ.filter fun x=>40*Real.log (Nat.card K)≤hits (RectangleGeometry.rectangle U) x
  let E:=badᶜ
  let p:Law (Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)):=iid (uniform Fintype.card_pos) (Fin N)
  have hbad : eventMass p bad≤6/(Nat.card K:ℝ)^7 := by
    have hh:=RectangleGeometry.rectangle_occupancy_tail hd N
      (by simpa only [hlog] using hN)
    convert hh using 1
    congr 1
    ext x
    simp [bad]
  have htail : 6/(Nat.card K:ℝ)^7≤1/2 := by
    have hq' : (3:ℝ)≤Nat.card K := by exact_mod_cast hq3
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hq' 7
    rw [div_le_iff₀ (pow_pos hqp 7)]
    norm_num at hp ⊢
    linarith
  have hmass : 1/2≤eventMass p E := by
    have hc : eventMass p E+eventMass p bad=1 := by
      convert eventMass_complement p bad using 1
      congr 2
      ext x
      simp [E]
    have hh:=hbad.trans htail
    linarith only [hc,hh]
  have hE : 0<eventMass p E := lt_of_lt_of_le (by norm_num) hmass
  let adm:=fun s : Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K) => ∀U : Submodule K (Dual K (Space K)),
    (∑i,if InRectangle U (s i).val.1.rep (s i).val.2.rep then (1:ℝ) else 0)≤40*σ
  have hgood : ∀s,s∈E→adm s := by
    intro s hs U
    have hh : ¬40*σ≤hits (RectangleGeometry.rectangle U) s := by
      intro hh
      exact Finset.mem_compl.mp hs (Finset.mem_biUnion.mpr ⟨U,Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hlog] using hh⟩⟩)
    have he : hits (RectangleGeometry.rectangle U) s=
        ∑i,if InRectangle U (s i).val.1.rep (s i).val.2.rep then (1:ℝ) else 0 := by
      simp only [hits,rectangle_mem_iff]
    rw [he] at hh
    exact (not_le.mp hh).le
  let P:=fun (s : Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)) (e : Fin n↪o Fin N) =>
    TupleIncident (fun i=>(s (e i)).val) ∧ TupleConsistent (fun i=>(s (e i)).val)
  let choose:=firstWitness hn P
  have hchoose : ∀s,P s (choose s) := fun s=>firstWitness_spec hn P s
    (independent_selector_of_not_cliqueFree s (hno s))
  let S:=initialSelectedStream adm E hE hgood choose Subtype.val encodeRaw encodeRaw_leftInverse
  have hgeom : Geometric S (40*σ) := by
    refine ⟨fun z _=>(hchoose z).1,fun z _=>(hchoose z).2,?_⟩
    intro z hz
    exact occupancy_reindex (fun i=>(z i).val) (choose z) (choose z).injective (40*σ)
      (hgood z (conditionOn_positive p E hE z hz).1)
  have hcap : Real.log (Fintype.card (FlagPair K (Space K)))≤
      Real.log (153*(Nat.card K:ℝ)^4)+10*σ := by
    have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
    have hj : Real.log 4≤Real.log (153*(Nat.card K:ℝ)^4) := by
      apply Real.log_le_log (by norm_num)
      have hh : (1:ℝ)≤(Nat.card K:ℝ)^4 := one_le_pow₀ hq1
      nlinarith
    have hh:=flagPair_log_card hd σ hs hq
    linarith
  let C : ContextDescription (κ:=Unit) S.law S.tuple 0
      (Real.log (153*(Nat.card K:ℝ)^4)+10*σ) :=
    { context:=fun _=>()
      domain:=fun _ _=>Finset.univ
      entropy_bound:=by simpa using entropy_le_log_card (map S.law (fun _=>()))
      contains:=by intros;exact Finset.mem_univ _
      cap:=by intros;simpa only [Finset.card_univ] using hcap }
  have hden : S.density≤2 := by
    change 1/eventMass p E≤2
    rw [div_le_iff₀ hE]
    linarith
  exact ⟨adm,⟨PolarState.of hd {
    sample:=Fin N→RectangleGeometry.Flag (K:=K) (V:=Space K)
    stream:=S
    code:=Unit
    description:=C
    density_bound:=hden
    geometric:=hgeom }⟩⟩
end
end FlagConstruction

open Filter
open scoped Topology
noncomputable section
lemma initial_floor_scales {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,
      1≤σ ∧ 3≤Real.exp σ ∧
      ⌊Real.exp σ*σ^(1+η)⌋₊≤⌊(Real.exp σ)^4*σ⌋₊ ∧
      (1/2:ℝ)*Real.exp σ*σ^(1+η)≤(⌊Real.exp σ*σ^(1+η)⌋₊:ℝ) := by
  have hg : Tendsto (fun σ : ℝ=>Real.exp σ) atTop atTop := Real.tendsto_exp_atTop
  filter_upwards [eventually_ge_atTop (1:ℝ),hg.eventually_ge_atTop 3] with σ hs hq
  have hsp : 0<σ := zero_lt_one.trans_le hs
  have hqp : 0<Real.exp σ := Real.exp_pos _
  have ht : 1≤σ^(1+η) := Real.one_le_rpow hs (by linarith)
  have hp : σ^η≤σ := by
    nth_rw 2 [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have hσq : σ≤Real.exp σ := le_trans (by linarith : σ≤σ+1) (Real.add_one_le_exp σ)
  have hq1 : 1≤Real.exp σ := by linarith
  have hq3 : Real.exp σ≤(Real.exp σ)^3 := by
    have hh : 1≤(Real.exp σ)^2 := one_le_pow₀ hq1
    nlinarith
  have hp' : Real.exp σ*σ^(1+η)≤(Real.exp σ)^4*σ := by
    rw [Real.rpow_add hsp,Real.rpow_one]
    have hh:=mul_le_mul_of_nonneg_left (hp.trans (hσq.trans hq3))
      (show 0≤Real.exp σ*σ by positivity)
    nlinarith only [hh]
  have hlo : 2≤Real.exp σ*σ^(1+η) := by nlinarith
  have hf:=Nat.lt_floor_add_one (Real.exp σ*σ^(1+η))
  exact ⟨hs,hq,Nat.floor_mono hp',by linarith⟩
end

end SharpRamseyFive

end OAI
