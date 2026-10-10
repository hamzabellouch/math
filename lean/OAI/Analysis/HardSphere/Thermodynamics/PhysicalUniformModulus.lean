import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalAffinitySum
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalParameters
import OAI.Analysis.HardSphere.Allocation.PhysicalGroundSupply
import OAI.Analysis.HardSphere.Thermodynamics.PhysicalNumeric
import OAI.Analysis.HardSphere.Geometry.PhysicalPathComparison

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma allocated_group_floor {ell D : ℝ} {M : ℕ} (hell : 0<ell) (hD : 0<D) (hM : 0<M)
    (hlarge : 16*(M:ℝ)/ell≤D) :
    let G := ⌊ell*D/(4*M)⌋₊
    (G*M:ℝ)≤ell*D/2 ∧ ell/(8*M)≤(G:ℝ)/D := by
  dsimp only
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hx : 0≤ell*D/(4*M) := by positivity
  have hlo := Nat.lt_floor_add_one (ell*D/(4*M))
  have hhi := Nat.floor_le hx
  have hbig : 16*M≤ell*D := by
    have h := (div_le_iff₀ hell).mp hlarge
    nlinarith
  constructor
  · have hh := (le_div_iff₀ (by positivity : (0:ℝ)<4*M)).mp hhi
    nlinarith
  · apply (le_div_iff₀ hD).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<8*M)).mpr
    have hh := (div_lt_iff₀ (by positivity : (0:ℝ)<4*M)).mp hlo
    nlinarith

theorem physical_uniform_modulus :
    ∃A c D₀ : ℝ,2≤A ∧ 0<c ∧ 1≤D₀ ∧ ∃K₀ : ℕ,400≤K₀ ∧
    ∀{N K : ℕ} [Nontrivial (Fin (N+1))] [NeZero K] {L : Length},
    ∀_hL : L.val=(K:ℝ),K₀≤K → ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 →
    D₀≤D → A/2≤α → α≤2*A → ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
    c≤Phase.modulusOccupation
      (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  obtain ⟨p₀,κ,hp₀,hκ,Kc,hpath⟩ := physical_path_comparison
  obtain ⟨A,ell,b,H,t₀,hA2,hell,hb,hH,ht₀,hsupply⟩ := physical_ground_bad_supply
  have hA : 0<A := by linarith
  let t := t₀/2
  have ht : 0<t := by dsimp [t]; positivity
  let B := (routeDensityBound t).toReal
  have hB : 1≤B := by
    have hh := ENNReal.toReal_mono (routeDensityBound_ne_top ht) (one_le_routeDensityBound t)
    simpa only [ENNReal.toReal_one] using hh
  have hBt : routeDensityBound t≤ENNReal.ofReal B := by
    rw [ENNReal.ofReal_toReal (routeDensityBound_ne_top ht)]
  obtain ⟨q,hq,hpow,δ,hδ,hδ1,hcost⟩ := choose_physical_group hp₀ hκ hB
  let M := 2*q
  have hM : 0<M := by dsimp [M]; omega
  let p := min 1 (p₀/12)
  have hp : 0<p := lt_min zero_lt_one (by positivity)
  have hp1 : p≤1 := min_le_left _ _
  have hbad : 6*p+(2/5:ℝ)^q≤p₀ := by
    have hh : p≤p₀/12 := min_le_right _ _
    linarith
  obtain ⟨Ds,hDs,hsupply⟩ := hsupply t ht (by dsimp [t]; linarith) p hp hp1
  have hevent := (source_physical_scale (by positivity : 0<2*A) hb ht).and
    ((physical_collision_eventually (A:=2*A) (C:=64*(meanCost+1)) (by positivity) ht
      (by nlinarith [meanCost_nonneg]) hδ1 M).and
      (tendsto_inv_atTop_zero.eventually (gt_mem_nhds ht)))
  obtain ⟨Dg,hDg⟩ := Filter.eventually_atTop.mp hevent
  let D₀ := max Ds (max Dg (16*(M:ℝ)/ell))
  let c := ell/(128000*M*B)
  refine ⟨A,c,D₀,hA2,by dsimp [c]; positivity,hDs.trans (le_max_left _ _),
    max Kc 400,le_max_right _ _,?_⟩
  intro N K instN instK L hL hK D α hDeq hD hαlo hαhi ψ hψ
  have hDsD := (le_max_left Ds (max Dg (16*(M:ℝ)/ell))).trans hD
  have hDgD : Dg≤D := (le_max_left Dg _).trans ((le_max_right Ds _).trans hD)
  have hDlarge : 16*(M:ℝ)/ell≤D := (le_max_right Dg _).trans ((le_max_right Ds _).trans hD)
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one (hDs.trans hDsD)
  have hα : 0<α := lt_of_lt_of_le (by positivity : 0<A/2) hαlo
  obtain ⟨hscale,hcoll,htime⟩ := hDg D hDgD
  let w : Time := ⟨D⁻¹/t,⟨by positivity,(div_le_one ht).mpr htime.le⟩⟩
  have hw : t*(w:ℝ)=D⁻¹ := by dsimp only [w]; field_simp
  let G := ⌊ell*D/(4*M)⌋₊
  obtain ⟨hG,hGlow⟩ := allocated_group_floor hell hDp hM hDlarge
  let m := ⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊
  let R := D^(1/12:ℝ)
  let C := 64*(meanCost+1)
  let S := b*D^(-(1/3):ℝ)/8
  let s₀ := b*D^(-(1/3):ℝ)
  let u := prefixTime midpointTime w
  have h400 : 400≤K := (le_max_right Kc 400).trans hK
  have h1 : 1≤K := by omega
  have h100 : 100≤L.val := by rw [hL]; exact_mod_cast (show 100≤K by omega)
  have h50 : 50<L.val := by linarith
  refine physical_modulus_from_gains (G:=G) (M:=M) hL h400 hψ m t R C S s₀ ht.le u
    D ell B hDeq hell hM hB hGlow ?_
  intro ij hij g
  have hjoint : ∀T : Finset (Fin 3→Fin K),
      physicalDatumLaw (M:=M) g ψ m (α/D) R C S s₀ (2*t) u
        {d | T⊆datumBad hL g m t (α/D) R C S u d}≤
      (ENNReal.ofReal (6*p+(2/5:ℝ)^q))^T.card := by
    intro T
    have hh := hsupply hL h100 D α (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq) hDsD hαlo hαhi w hw (show (G:ℝ)*(2*q)≤ell*D/2 by simpa only [G,M,Nat.cast_mul,Nat.cast_ofNat] using hG) ψ hψ g T
    simpa only [ENNReal.ofReal_add (by positivity : 0≤6*p) (by positivity : 0≤(2/5:ℝ)^q),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6),ENNReal.ofReal_ofNat] using hh
  obtain ⟨σ,hσ,hm,hest⟩ := hpath K ((le_max_left Kc 400).trans hK) instK hL h1 h50 hψ
    g m t R C S s₀ D⁻¹ u (hscale α hα hαhi w hw)
    (6*p+(2/5:ℝ)^q) (by positivity) hbad hjoint hM δ B hδ hB hBt (by simpa only [M,Nat.cast_mul,Nat.cast_ofNat] using hcost)
    (hcoll α hα hαhi) ij.1 ij.2 ((Finset.mem_filter.mp hij).2)
  let := hσ
  obtain ⟨hP,hpP,hipP,hmP⟩ := hest true
  obtain ⟨hQ,hpQ,hipQ,hmQ⟩ := hest false
  let := hP
  let := hQ
  exact actual_common_gain σ _ _ hB hm hpP hpQ hipP hipQ hmP hmQ

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
open BathSlice
attribute [local instance] Classical.propDecidable

lemma omitted_integral_real {n : ℕ} {L : Length} (h r : ℝ) (μ : Measure (Configuration n L))
    {C : ℝ} (hC : 0≤C) (hbound : (∫⁻Y,(volume : Measure (Torus L)) (omitted h r Y) ∂μ)≤ENNReal.ofReal C) :
    (∫Y,(volume : Measure (Torus L)).real (omitted h r Y) ∂μ)≤C := by
  have hm := measurable_omitted_volume (n:=n) L h r
  have hf : (∫⁻Y,(volume : Measure (Torus L)) (omitted h r Y) ∂μ)≠⊤ :=
    ne_of_lt (hbound.trans_lt ENNReal.ofReal_lt_top)
  have he := integral_toReal hm.aemeasurable (ae_lt_top hm hf)
  change (∫Y,((volume : Measure (Torus L)) (omitted h r Y)).toReal ∂μ)≤C
  rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hC)

theorem physical_geometry_error : ∃Q : ℕ,0<Q ∧ ∀θ : ℝ,0<θ →
    ∃b H : ℝ,0<b ∧ b≤1/4 ∧ 0<H ∧
      Tendsto (fun D : ℝ ↦ ((H/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀A : ℝ,∃D₀ : ℝ,1≤D₀ ∧
    ∀{N K : ℕ} [NeZero K] {L : Length},∀_hL : L.val=(K:ℝ),
      100≤L.val → ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤A →
      α/D≤1/4096 → 6*(α/D)≤ spatialCloseScale D b → θ*D≤1/(1372*(α/D)) →
    ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
    let p := ((H/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))
    8*(2^27:ℝ)*p≤1/2 →
    (∫Y,(volume : Measure (Torus L)).real (omitted (microMesh (α/D)) (α/D) Y)
      ∂(groundPositionLaw (N+1) L ψ).map (fun X ↦ fun i : Fin N ↦ X i.succ))/L.val^3 ≤
      1029*α^2/D+128*(2^27:ℝ)*p+(K:ℝ)^3*((2^27:ℝ)*p)^K := by
  obtain ⟨Q,hQ,htail⟩ := physical_omitted_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,H,hb,hb1,hH,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,H,hb,hb1,hH,hlim,?_⟩
  intro A
  obtain ⟨D₀,hD₀,hfin⟩ := hfin A
  refine ⟨D₀,hD₀,?_⟩
  intro N K instK L hL h100 D α hDeq hD hα hαA hrs hsep hθD ψ hψ p hp
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one (hD₀.trans hD)
  have hαp : 0<α := lt_of_lt_of_le zero_lt_one hα
  have hp0 : 0≤p := Real.rpow_nonneg (by positivity) _
  have h1 : 1≤K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  let e : Fin N ↪ Fin (N+1) := ⟨Fin.succ,Fin.succ_injective N⟩
  have hpE : 8*((2^27:ℕ):ℝ≥0∞)*ENNReal.ofReal p≤(2:ℝ≥0∞)⁻¹ := by
    have hh := ENNReal.ofReal_le_ofReal hp
    simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤8*2^27),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤8),ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
      ENNReal.ofReal_one,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),one_div,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hh := hfin (N+1) K K L hL D α h100 (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq) hD hα hαA hrs hsep hθD ψ hψ N e h1 le_rfl hpE
  let C := 1029*(α/D)^2*N+(K:ℝ)^3*(128*((2^27:ℝ)*p))+L.val^3*(K:ℝ)^3*((2^27:ℝ)*p)^K
  have hC : 0≤C := by dsimp only [C]; positivity
  have hh' : (∫⁻ Y,(volume : Measure (Torus L)) (omitted (microMesh (α/D)) (α/D) Y)
      ∂(groundPositionLaw (N+1) L ψ).map (fun X ↦ fun i : Fin N ↦ X i.succ))≤ENNReal.ofReal C := by
    dsimp only [C]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(K:ℝ)^3),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤128),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤2^27),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤L.val^3*(K:ℝ)^3),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤L.val^3),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤K),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤2),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤2^27*p),
      ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
    simpa only [Nat.cast_pow,Nat.cast_ofNat,p,e,Function.Embedding.coeFn_mk] using hh
  have hreal := omitted_integral_real (microMesh (α/D)) (α/D) _ hC hh'
  refine (div_le_div_of_nonneg_right hreal (by positivity)).trans ?_
  have hn : (N:ℝ)≤D*L.val^3 := by rw [hDeq]; field_simp; norm_num
  have hfirst : 1029*(α/D)^2*(N:ℝ)/L.val^3≤1029*α^2/D := by
    apply (div_le_iff₀ (by positivity : 0<L.val^3)).mpr
    apply le_trans (mul_le_mul_of_nonneg_left hn (by positivity))
    field_simp
    ring_nf
    exact le_rfl
  dsimp only [C]
  rw [add_div,add_div]
  have htwo : (K:ℝ)^3*(128*((2^27:ℝ)*p))/L.val^3=128*(2^27:ℝ)*p := by rw [hL]; field_simp
  have hthree : L.val^3*(K:ℝ)^3*((2^27:ℝ)*p)^K/L.val^3=(K:ℝ)^3*((2^27:ℝ)*p)^K := by field_simp
  rw [htwo,hthree]
  linarith

end HardSphere
end
end

end OAI
