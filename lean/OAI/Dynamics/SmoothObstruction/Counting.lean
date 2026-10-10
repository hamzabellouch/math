import OAI.Dynamics.SmoothObstruction.DensityLocalization
import OAI.Dynamics.SmoothObstruction.SwitchScales

namespace OAI

section

namespace SmoothObstruction.EndpointBudget
open Set Filter Topology ExteriorStability
/-- The literal endpoint hypotheses, simultaneously at every rank of the
unchanged ambient dimension. -/
theorem eventual_admissible {α : Type*} {l : Filter α} {b n δ : α → ℝ}
    (hbpos : ∀ᶠ k in l,0<b k) (hb : Tendsto b l (𝓝 0))
    (hn : Tendsto n l atTop) (hfloor : ∀ᶠ k in l,n k^(-1/10:ℝ)≤b k)
    (d : ℕ) (Dg R C K₀ Crel C₁ c β : ℝ) (hc : 0<c) (hβ : 0<β)
    (hδ : ∀ᶠ k in l,0≤δ k ∧ δ k≤Real.exp (-c*b k^(3/4:ℝ)*n k)) :
    ∀ᶠ k in l,∀ p≤d,
      admissible d p Dg R C K₀ Crel C₁ (b k) (n k) (b k^(1/2:ℝ)) (δ k) β := by
  have he := all_ranks hbpos hb hn hfloor d C Crel C₁ (d*R) K₀ Dg c hc
    (fun p : Fin (d+1) => frameWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) p.val)
    (fun p : Fin (d+1) => (Fintype.card (powersetCard (Fin d) p.val):ℝ))
    (fun p : Fin (d+1) => ‖continuousWedge (E:=EuclideanSpace ℝ (Fin d)) p.val‖)
    (fun p : Fin (d+1) => unitWedgeConstant (E:=EuclideanSpace ℝ (Fin d)) p.val)
    (fun _ => β)
    (fun p => (by norm_num : (0:ℝ)≤1).trans (one_le_frameWedgeConstant p.val))
    (fun p => Nat.cast_nonneg _) (fun p => ContinuousMultilinearMap.opNorm_nonneg _) 
    (fun p => (by norm_num : (0:ℝ)≤1).trans (one_le_unitWedgeConstant p.val))
    (fun _ => hβ) hδ
  filter_upwards [he] with k hk
  intro p hp
  have h := hk ⟨p,by omega⟩
  simpa only [admissible,leading,normCost,mixedCost,relative,graph,mul_assoc] using h
end SmoothObstruction.EndpointBudget

namespace SmoothObstruction.GridCount
open Filter Topology
lemma ceil_grid_bound {A t : ℝ} (hA : 0≤A) (ht : 0≤t) :
    ((2*⌈A*Real.exp t+1⌉₊+1:ℕ):ℝ)≤(2*A+5)*Real.exp t := by
  have hh := Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤A*Real.exp t+1)
  have he := Real.one_le_exp_iff.mpr ht
  push_cast
  nlinarith

/-- A uniform exponential count for the two original starting grids.
The strip-thinning denominator N cancels from the actual grid period. -/
theorem original_grid_count (d j : ℕ) (Dc Dp Dg : ℝ) (hDc : 1≤Dc) (hDp : 1≤Dp) (hDg : 0≤Dg) :
    ∃ C : ℝ,0≤C ∧ ∀ (b : ℝ) (n N : ℕ),0<b → b≤1 → 1≤b*n → 0<N →
      let B := Dg*(b*n)
      let t := b^(1/8:ℝ)*n
      let dc := Real.exp (-t)/(((d:ℝ)+1)*N)
      let dp := Real.exp (-2*t)/(Real.sqrt 2*((d:ℝ)+1)*N)
      let mc := ⌈Dc/(dc*N)+1⌉₊
      let mp := ⌈(Real.sqrt 2*Real.exp (2*B))*Dp/(dp*N)+1⌉₊
      ((j*(2*mc+1)^d*(2*mp+1)^d:ℕ):ℝ)≤Real.exp (C*t) := by
  let A₁ := Dc*((d:ℝ)+1)
  let A₂ := 2*Dp*((d:ℝ)+1)
  let K := (j:ℝ)*(2*A₁+5)^d*(2*A₂+5)^d
  have hA₁ : 0≤A₁ := by dsimp only [A₁]; positivity
  have hA₂ : 0≤A₂ := by dsimp only [A₂]; positivity
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨K+(3+2*Dg)*d,by positivity,?_⟩
  intro b n N hb hb1 hbn hN B t dc dp mc mp
  have hbroot : b≤b^(1/8:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hb hb1 (by norm_num : (1/8:ℝ)≤1)
  have htn : b*n≤t := mul_le_mul_of_nonneg_right hbroot (Nat.cast_nonneg _)
  have ht : 1≤t := hbn.trans htn
  have hB : B≤Dg*t := mul_le_mul_of_nonneg_left htn hDg
  have hB0 : 0≤B := by dsimp only [B]; positivity
  have hcs : Dc/(dc*N)=A₁*Real.exp t := by
    dsimp only [dc,A₁]
    rw [Real.exp_neg]
    field_simp
  have hps : (Real.sqrt 2*Real.exp (2*B))*Dp/(dp*N)=A₂*Real.exp (2*B+2*t) := by
    dsimp only [dp,A₂]
    rw [show -2*t= -(2*t) by ring,Real.exp_neg,Real.exp_add]
    have hs : Real.sqrt 2*Real.sqrt 2=2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith only [hs]
  have hc := ceil_grid_bound hA₁ (by linarith : 0≤t)
  have hp := ceil_grid_bound hA₂ (by linarith : 0≤2*B+2*t)
  rw [←hcs] at hc
  rw [←hps] at hp
  have hcp := pow_le_pow_left₀ (Nat.cast_nonneg _) hc d
  have hpp := pow_le_pow_left₀ (Nat.cast_nonneg _) hp d
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hcp (Nat.cast_nonneg j)) hpp
    (by positivity) (by positivity)
  have hmain : ((j*(2*mc+1)^d*(2*mp+1)^d:ℕ):ℝ)≤K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := by
    calc
      _ ≤ (j:ℝ)*((2*A₁+5)*Real.exp t)^d*((2*A₂+5)*Real.exp (2*B+2*t))^d := by
        simpa only [Nat.cast_mul,Nat.cast_pow] using hm
      _ = K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := by
        dsimp only [K]
        rw [mul_pow,mul_pow,←Real.exp_nat_mul,←Real.exp_nat_mul,Real.exp_add]
        ring
  have hKexp : K≤Real.exp K := by linarith [Real.add_one_le_exp K]
  have hKt : K≤K*t := le_mul_of_one_le_right hK ht
  have hBd := mul_le_mul_of_nonneg_left hB (show 0≤2*(d:ℝ) by positivity)
  calc
    _ ≤ K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := hmain
    _ ≤ Real.exp K*Real.exp ((d:ℝ)*t+(d:ℝ)*(2*B+2*t)) := mul_le_mul_of_nonneg_right hKexp (Real.exp_pos _).le
    _ = Real.exp (K+((d:ℝ)*t+(d:ℝ)*(2*B+2*t))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((K+(3+2*Dg)*d)*t) := by apply Real.exp_le_exp.mpr; nlinarith only [hKt,hBd]
end SmoothObstruction.GridCount

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

omit [ProperSpace M] [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M] in
lemma interior_of_selected_ball (a x : M) (hx : x∈(chartAt H a).source) {r : ℝ} (hr : 0≤r)
    (hs : closedBall ((extChartAt I a) x) r⊆interior (range I)) : I.IsInteriorPoint x := by
  apply (I.isInteriorPoint_iff_of_mem_atlas (n:=∞) (by simp) (chart_mem_atlas H a) hx).mpr
  exact (chartAt H a).mem_interior_extend_target ((chartAt H a).map_source hx)
    (hs (mem_closedBall_self hr))

/-- Finite translates, canonical references, the original retained carrier,
and the genuine global switch are compatible at all sufficiently large scales.
The explicit cell cardinality counts only two starting grids, never orbit labels. -/
theorem grid_switches (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (S : Diffeomorph I I M M ∞) (hS : MeasurePreserving S μ μ)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) (c : M → ι) (hc : Measurable c)
    (hcover : ∀ x,x∈K (c x)) (V : Set M) (hV : MeasurableSet V)
    (s : ℝ) (hs : 0<s) (hcore : ∀ x∈V,∀ y,dist y x ≤ s → c y=c x)
    (η : ℝ) (hη : 0<η) (hVm : μ.real Vᶜ≤η/100)
    (b : ℕ → ℝ) (n : ℕ → ℕ) (hbpos : ∀ k,0<b k) (hb : Tendsto b atTop (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) atTop atTop)
    (hfloor : ∀ k,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (Dg R₀ : ℝ) (hDg : 0≤Dg) (hR₀ : 0≤R₀)
    (G : ℕ → Set M) (hG : ∀ k,MeasurableSet (G k)) (hGm : ∀ k,μ.real (G k)ᶜ≤η/100)
    (hA : ∀ᶠ k in atTop,∀ x∈G k,Nonempty (BilateralGauge I S a c (n k) (Dg*(b k*n k)) R₀ x))
    (Cb : ℝ) (_ : 0≤Cb)
    (hcollar : ∀ r : ℝ,0≤r → ∃ W : Set M,MeasurableSet W ∧ μ.real W≤Cb*r ∧
      ∀ i x,x∈K i → x∉W → closedBall ((extChartAt I (a i)) x) r⊆interior (range I)) :
    ∃ (Dc Dp : ℝ) (N : ℕ) (ρ : ℕ → ℝ),1≤Dc ∧ 1≤Dp ∧ 0<N ∧
      Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
      let B := Dg*(b k*n k)
      let h₀ := Real.exp (-b k^(1/8:ℝ)*n k)
      let r := Real.exp (-2*b k^(1/8:ℝ)*n k)
      let δc := h₀/(((d:ℝ)+1)*N)
      let δp := r/(Real.sqrt 2*((d:ℝ)+1)*N)
      let mc := ⌈Dc/(δc*N)+1⌉₊
      let mp := ⌈(Real.sqrt 2*Real.exp (2*B))*Dp/(δp*N)+1⌉₊
      ∃ (J : Type) (_ : Fintype J) (_ : MeasurableSpace J) (_ : MeasurableSingletonClass J)
        (L : M → J) (Gp : Set (M×M)) (Φ : M×M → M×M),
        Fintype.card J=Fintype.card ι*(2*mc+1)^d*(2*mp+1)^d ∧
        Measurable L ∧ MeasurableSet Gp ∧ Measurable Φ ∧
        1-η≤(PairLaw.law μ L).real Gp ∧
        ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2:ℝ≥0∞) • μ ∧
        ∀ u∈Gp,originalTube I S a c (n:=n k) (ρ k) u.1 (Φ u).1 ∧
          originalTube I S.symm a c (n:=n k) (ρ k) u.2 (Φ u).1 := by
  classical
  obtain ⟨r₀,C₀,σ,r₁,C₁,rg,Cg,β,K₀F,CreF,C₁F,K₀B,CreB,C₁B,rμ,
    hr₀,hC₀,hσ,hr₁,hC₁,hrg,hCg,hβ,hKF,hCrF,hCF,hKB,hCrB,hCB,hrμ,hswitch⟩ :=
    genuine_pair_switch I hclosed μ hμ S a K hK hKU s Dg hs hDg
  obtain ⟨Dc,hDc,hcoarse⟩ := ChartDensity.exists_coarse_cells I μ a K hK hKU c hc hcover
  obtain ⟨Dp,hDp,hproduct⟩ := finite_product_partition_uniform I μ S a K hK hKU c hcover
  obtain ⟨N,hN⟩ := exists_nat_gt ((d:ℝ)/(η/100)+1)
  have hNpos : 0<N := by
    have : 0≤(d:ℝ)/(η/100) := by positivity
    exact_mod_cast (by linarith : (0:ℝ)<N)
  have hNm : (d:ℝ)/N≤η/100 := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hNpos)).mpr
    have h := (div_le_iff₀ (by positivity : (0:ℝ)<η/100)).mp (show (d:ℝ)/(η/100)≤N by linarith)
    simpa only [mul_comm] using h
  let Ac : ℝ := ((d:ℝ)+1)*N
  let Ap : ℝ := Real.sqrt 2*((d:ℝ)+1)*N
  have hAc : 0<Ac := by dsimp only [Ac]; positivity
  have hAp : 0<Ap := by dsimp only [Ap]; positivity
  let BB (k : ℕ) := Dg*(b k*n k)
  let g (k : ℕ) := b k^(1/2:ℝ)
  let α (k : ℕ) := (2+8*(d:ℝ))*g k
  let ε (k : ℕ) := Real.exp (-b k^(3/4:ℝ)*n k)
  let h₀ (k : ℕ) := Real.exp (-b k^(1/8:ℝ)*n k)
  let r (k : ℕ) := Real.exp (-2*b k^(1/8:ℝ)*n k)
  let δ (k : ℕ) := Real.exp (-(3/2:ℝ)*b k^(1/8:ℝ)*n k)
  let ρ (k : ℕ) := 2*C₀*ShortBin.bvpInverseBound (BB k) (α k) (n k)*r k
  have hbfe : ∀ᶠ k in atTop,0<b k := Filter.Eventually.of_forall hbpos
  have hffe : ∀ᶠ k in atTop,(n k:ℝ)^(-1/10:ℝ)≤b k := Filter.Eventually.of_forall hfloor
  have hεenv : ∀ᶠ k in atTop,0≤ε k ∧ ε k≤Real.exp (-b k^(3/4:ℝ)*n k) :=
    Filter.Eventually.of_forall (fun k => ⟨(Real.exp_pos _).le,le_rfl⟩)
  have hρ0 := (ShortBin.spatial_switch_limits hbfe hb hn hffe hεenv Dg (2+8*(d:ℝ)) C₀ hDg (by positivity)).2.2.1
  have hspatial := ShortBin.spatial_ready hbfe hb hn hffe Dg (2+8*(d:ℝ)) C₀ C₁ Cg K₀F K₀B
    r₀ rg σ r₁ rμ Ac Ap hDg (by positivity) hC₀ hr₀ hrg hσ hr₁ hrμ hAc hAp
  have hrefs := eventual_finite_references I hclosed S a K hK hKU hbfe hb hn hffe Dg R₀ hDg
  choose Cp hCp hCpbound using fun p : Fin (d+1) =>
    ExteriorStability.exists_power_bound (E:=EuclideanSpace ℝ (Fin d)) p.val
  let Cext := 1+∑ p,Cp p
  have hCext : 0≤Cext := by
    have := Finset.sum_nonneg (s:=Finset.univ) (fun p _ => (show (0:ℝ)≤1 by norm_num).trans (hCp p))
    dsimp only [Cext]
    linarith
  have hpoly (p : ℕ) (hp : p≤d) (F : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      ‖ExteriorStability.exterior p F‖≤Cext*(max 1 ‖F‖)^p := by
    have hh := hCpbound ⟨p,by omega⟩ F
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hc := Finset.single_le_sum (fun q _ => (show (0:ℝ)≤1 by norm_num).trans (hCp q)) (Finset.mem_univ (⟨p,by omega⟩ : Fin (d+1)))
    dsimp only [Cext]; linarith
  have hbudgetF := EndpointBudget.eventual_admissible hbfe hb hn hffe d Dg R₀ Cext K₀F CreF C₁F 1 β (by norm_num) hβ
    (by simpa only [neg_one_mul] using hεenv)
  have hbudgetB := EndpointBudget.eventual_admissible hbfe hb hn hffe d Dg R₀ Cext K₀B CreB C₁B 1 β (by norm_num) hβ
    (by simpa only [neg_one_mul] using hεenv)
  have hdec (m : ℕ) : Tendsto (fun k => (n k:ℝ)^m*h₀ k) atTop (𝓝 0) := by
    have hh := ScaleHierarchy.polynomial_decay (p:=1/8) (q:=1) (c:=1) (C:=0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbfe hb hn hffe m
    simpa only [zero_mul,zero_sub,one_mul,neg_mul,h₀] using hh
  have hcollar0 : Tendsto (fun k => (2*(n k:ℝ)+3)*(Cb*h₀ k)) atTop (𝓝 0) := by
    have hh := ((hdec 1).const_mul (2*Cb)).add ((hdec 0).const_mul (3*Cb))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'; apply Filter.Eventually.of_forall; intro k; simp only [pow_one,pow_zero,one_mul]; ring
  refine ⟨Dc,Dp,N,ρ,hDc,hDp,hNpos,hρ0,?_⟩
  filter_upwards [hspatial,hrefs,hbudgetF,hbudgetB,hA,
    hcollar0.eventually_le_const (by positivity : (0:ℝ)<η/100)] with k hsp href hbudF hbudB hAk hcolmass
  rcases hsp with ⟨hbn,heps,hsmall,hgap,hδr,hδrg,hρδ,hρσ,hρc,hρr₁,hρC,hρCg,hδF,hδB,hE,hcontract,hdata,hrrμ,hδh⟩
  dsimp only
  let dc := h₀ k/Ac
  let dp := r k/Ap
  have hdc : 0<dc := div_pos (Real.exp_pos _) hAc
  have hdp : 0<dp := div_pos (Real.exp_pos _) hAp
  obtain ⟨P,Wc,hP,hWc,hWcm,hPc,hPdiam,hPrec,hPcard⟩ := hcoarse hdc hNpos
  let C := ι × (Fin d → Fin (2*⌈Dc/(dc*N)+1⌉₊+1))
  have hPc' (x y : M) (he : P x=P y) : c x=c y := by rw [←hPc x,←hPc y,he]
  have hsrc (x : M) : x∈(extChartAt I (a (c x))).source := by rw [extChartAt_source]; exact hKU _ (hcover x)
  have hceq : ((d:ℝ)+1)*(dc*N)=h₀ k := by dsimp only [dc,Ac]; field_simp
  have hpeq : Real.sqrt 2*((d:ℝ)+1)*(dp*N)=r k := by dsimp only [dp,Ap]; field_simp
  obtain ⟨Wb,hWb,hWbm,hWs⟩ := hcollar (h₀ k) (Real.exp_pos _).le
  let G' := G k\Wb
  have hiG (x : M) (hx : x∈G') : I.IsInteriorPoint x :=
    interior_of_selected_ball I _ _ (hKU _ (hcover x)) (Real.exp_pos _).le (hWs _ x (hcover x) hx.2)
  let A (x : G') : BilateralGauge I S a c (n k) (BB k) R₀ x := (hAk x x.property.1).some
  have hco (x y : M) (he : P x=P y) :
      ‖(extChartAt I (a (c y))) x-(extChartAt I (a (c y))) y‖≤h₀ k := by
    have hh := hPdiam x y he
    rw [hceq] at hh
    rw [ChartDensity.coordinates_eq I _ _ (hsrc x),hPc' x y he] at hh
    rw [ChartDensity.coordinates_eq I _ _ (hsrc y)] at hh
    exact hh
  obtain ⟨γ,T,ref,Wf,Wback,hrefeq,hα,hrefP,hcard,hreff,hslow,hfast,hstart,hend⟩ :=
    href C c P G' A hcover hPc' hiG hco
  subst ref
  have hBB : 0≤BB k := mul_nonneg hDg (mul_nonneg (hbpos k).le (Nat.cast_nonneg _))
  obtain ⟨L,Wp,hL,hWp,hWpm,hLP,hLdiam,hLrec,hLcard⟩ :=
    hproduct C P hP Prod.fst hPc G' (n k) (BB k) R₀ hBB A T dp hdp N hNpos
  have hSsymm : MeasurePreserving S.symm μ μ := MeasurePreserving.symm S.toHomeomorph.toMeasurableEquiv hS
  obtain ⟨R,hR,hRG,hRm,hret⟩ := RetainedGlobal.exists_retained μ S S.symm hS hSsymm
    G' V Wc Wp Wb ((hG k).diff hWb) hV hWc hWp hWb (n k)
  have hmassR : μ.real Rᶜ≤η/2 := by
    have hG'm : μ.real G'ᶜ≤μ.real (G k)ᶜ+μ.real Wb := by
      simpa only [G',compl_sdiff,union_comm] using RetainedGlobal.real_union_le μ (G k)ᶜ Wb
    have hcoef : 0≤2*(n k:ℝ)+3 := by positivity
    have hbc := mul_le_mul_of_nonneg_left hWbm hcoef
    have hWc' := hWcm.trans hNm
    have hWp' := hWpm.trans hNm
    have hg' := hGm k
    nlinarith only [hRm,hG'm,hbc,hWc',hWp',hVm,hg',hcolmass,hη]
  have hLp (x y : M) (he : L x=L y) : P x=P y := by rw [←hLP x,←hLP y,he]
  have hLc (x y : M) (he : L x=L y) : c x=c y := hPc' x y (hLp x y he)
  have hLdiam' (x y : M) (he : L x=L y) :
      ‖ChartDensity.coordinates I (a (c x)) x-ChartDensity.coordinates I (a (c x)) y‖≤r k := by
    simpa only [hpeq] using hLdiam x y he
  obtain ⟨Φ,hΦ,hGp,hinj,hlaw,hmarg,htube⟩ := hswitch (C:=C) c P L Prod.fst Prod.fst G' R V Wc Wp
    (n k) (b k) R₀ Cext (ε k) (g k) (α k) (r k) dc dp
    (Real.sqrt 2*Real.exp (2*BB k)) γ A T (fun x => (FiniteBins.reference P G' (FiniteBins.key P G' x)).val) Wf Wback hc hP hL hR hRG hcover hLP hPc
    (fun x hx => hiG x (hRG hx)) hrefP hcard hreff (by simpa only [ε,SwitchScales.shortSignal,neg_mul] using hstart) hend
    (hbpos k).le hbn hR₀ hCext (Real.exp_pos _).le heps hsmall (Real.rpow_nonneg (hbpos k).le _)
    hslow hfast hgap (fun x => hα (P x)) (Real.exp_pos _).le hδr hδrg
    (by exact mul_nonneg (mul_nonneg (by linarith) (ShortBin.bvp_nonneg _ _ _)) (Real.exp_pos _).le)
    hρδ hρσ hρc hρr₁ hρC hρCg hδF hδB hdc (by positivity) hE hpoly hbudF hbudB
    (fun x hx t => ⟨(closedBall_subset_closedBall hδh).trans (hWs _ _ (hcover _) ((hret x hx).2.2.2.2.2.2.2 _ (by omega)).1),
      (closedBall_subset_closedBall hδh).trans (hWs _ _ (hcover _) ((hret x hx).2.2.2.2.2.2.2 _ (by omega)).2)⟩)
    (fun x hx y hy he => by
      have hh := hLdiam' x y he
      rw [ChartDensity.coordinates_eq I _ _ (hsrc x),hLc x y he,
        ChartDensity.coordinates_eq I _ _ (hsrc y),norm_sub_rev] at hh
      rw [hLc x y he]
      exact hh.trans (le_mul_of_one_le_left (Real.exp_pos _).le hC₀))
    hcontract hdata (fun x y he => (hLdiam' x y he).trans_lt hrrμ) hcore hPrec
    (fun x y z hx he hxW hyW hz herr => by
      apply hLrec x y z (hRG hx) he hxW hyW hz
      exact herr)
    (fun x hx => ⟨(hret x hx).1,(hret x hx).2.1,(hret x hx).2.2.1,
      (hret x hx).2.2.2.1,(hret x hx).2.2.2.2.1,(hret x hx).2.2.2.2.2.1,(hret x hx).2.2.2.2.2.2.1⟩)
  let Gp := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
  have hmass := (RetainedGlobal.pair_mass μ L hL R hR hmassR).2
  refine ⟨_,inferInstance,inferInstance,inferInstance,L,Gp,Φ,?_,hL,hGp,hΦ,?_,hmarg,htube⟩
  · exact hLcard.trans (by rw [hPcard])
  · have he : Gp=R.prod R∩{u : M×M | L u.1=L u.2} := by
      ext u; exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,fun h => ⟨h.1.1,h.1.2,h.2⟩⟩
    rw [he]
    exact hmass
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal
variable {d : ℕ} {H : Type} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type} [MetricSpace M] [CompactSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]

/-- Smooth switching from a good gauge and a quantitative geometric
boundary collar, for Euclidean and half-space manifold models. -/
theorem switching_from_gauges (hclosed : IsClosed (range I))
    (μ : ProbabilityMeasure M) (hμ : SmoothPositiveDensity I (μ : Measure M))
    (S : Diffeomorph I I M M ∞) (hS : MeasurePreserving S (μ : Measure M) (μ : Measure M))
    (hcollar : ∀ (ι : Type) [Fintype ι] (a : ι → M) (K : ι → Set M),
      (∀ i,IsCompact (K i)) → (∀ i,K i⊆(chartAt H (a i)).source) →
      ∃ Cb : ℝ,0≤Cb ∧ ∀ r : ℝ,0≤r → ∃ W : Set M,MeasurableSet W ∧
        (μ : Measure M).real W≤Cb*r ∧
        ∀ i x,x∈K i → x∉W → closedBall ((extChartAt I (a i)) x) r⊆interior (range I)) :
    SmoothSwitching (μ : Measure M) S S.symm := by
  classical
  intro η hη
  let ε : ℝ≥0 := ⟨η/100,by positivity⟩
  obtain ⟨ι,hfin,hmeas,hsc,a,K,L,c,s,hK,hKU,hc,hcover,hL,hLm,hs,hLK,hLc,hcore,
    b,R₀,Dg,G,hR₀,hDg,hbpos,hfloor,hbs,hG,hA⟩ := good_stable_gauges I S μ hS hη ε (by change (0:ℝ)<η/100; positivity)
  let : Fintype ι := hfin
  let : MeasurableSpace ι := hmeas
  let : MeasurableSingletonClass ι := hsc
  let V := ⋃ i,L i
  have hV : MeasurableSet V := (isCompact_iUnion hL).measurableSet
  have hVm : (μ : Measure M).real Vᶜ≤η/100 := by
    exact (ENNReal.toReal_mono (by simp) hLm).trans_eq (by rfl)
  have hGm : ∀ k,(μ : Measure M).real (G k)ᶜ≤η/100 := by
    intro k
    rw [measureReal_compl (hG k).1.measurableSet,probReal_univ]
    have hh := (hG k).2
    linarith
  have hb : Tendsto b atTop (𝓝 0) := by
    have hh := hbs.tendsto_atTop_zero.sqrt
    simpa only [Real.sqrt_sq (hbpos _).le,Real.sqrt_zero] using hh
  have hn : Tendsto (fun k => ((2^k:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hfloor' : ∀ k,((2^k:ℕ):ℝ)^(-1/10:ℝ)≤b k := by
    intro k
    have he : ((2^k:ℕ):ℝ)^(-1/10:ℝ)=GoodStationary.floorAt k := by
      rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      dsimp only [GoodStationary.floorAt]
      congr 1
      ring
    rw [he]
    exact hfloor k
  obtain ⟨Cb,hCb,hcol⟩ := hcollar ι a K hK hKU
  obtain ⟨Dc,Dp,N,ρ,hDc,hDp,hN,hρ,hsw⟩ := grid_switches I hclosed (μ : Measure M) hμ S hS
    a K hK hKU c hc hcover V hV s hs hcore η hη hVm b (fun k => 2^k) hbpos hb hn hfloor'
    Dg R₀ hDg hR₀ G (fun k => (hG k).1.measurableSet) hGm (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hA)
    Cb hCb hcol
  obtain ⟨C,hC,hcount⟩ := GridCount.original_grid_count d (Fintype.card ι) Dc Dp Dg hDc hDp hDg
  let B := fun k => SmoothScales.B (b k)
  have hBs : Summable (fun k => (B k)^16) := by
    simpa only [B,SmoothScales.root_sixteen (hbpos _).le] using hbs
  have hex : ∀ᶠ k in atTop,∃ D : SwitchData (μ : Measure M),D.Good η C (B k) (2^k) ∧
      ∀ u∈D.carrier,originalTube I S a c (n:=2^k) (ρ k) u.1 (D.point u) ∧
        originalTube I S.symm a c (n:=2^k) (ρ k) u.2 (D.point u) := by
    filter_upwards [hsw,hb.eventually_le_const (by norm_num : (0:ℝ)<1)] with k hk hb1
    obtain ⟨J,hjfin,hjmeas,hjsc,P,Gp,Φ,hcard,hP,hGp,hΦ,hm,hmarg,ht⟩ := hk
    let : Fintype J := hjfin
    let : MeasurableSpace J := hjmeas
    let : MeasurableSingletonClass J := hjsc
    let D : SwitchData (μ : Measure M) := ⟨J,hjfin,hjmeas,hjsc,P,Gp,(fun u => (Φ u).1),hP,hGp,measurable_fst.comp hΦ⟩
    have hbn := GoodStationary.burden_ge_one b hfloor k
    have hcnt := hcount (b k) (2^k) N (hbpos k) hb1 (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hbn) hN
    refine ⟨D,⟨?_,hm,hmarg⟩,ht⟩
    change (Fintype.card J:ℝ)≤_
    rw [hcard]
    simpa only [B,SmoothScales.B,mul_assoc,neg_mul] using hcnt
  let D₀ : SwitchData (μ : Measure M) := ⟨Unit,inferInstance,inferInstance,inferInstance,
    (fun _ => ()),∅,Prod.fst,measurable_const,MeasurableSet.empty,measurable_fst⟩
  let D (k : ℕ) : SwitchData (μ : Measure M) :=
    if hk : ∃ D : SwitchData (μ : Measure M),D.Good η C (B k) (2^k) ∧
      ∀ u∈D.carrier,originalTube I S a c (n:=2^k) (ρ k) u.1 (D.point u) ∧
        originalTube I S.symm a c (n:=2^k) (ρ k) u.2 (D.point u)
    then hk.choose else D₀
  have hD : ∀ᶠ k in atTop,(D k).Good η C (B k) (2^k) ∧
      ∀ u∈(D k).carrier,originalTube I S a c (n:=2^k) (ρ k) u.1 ((D k).point u) ∧
        originalTube I S.symm a c (n:=2^k) (ρ k) u.2 ((D k).point u) := by
    filter_upwards [hex] with k hk
    dsimp only [D]; rw [dite_eq_left hk]; exact hk.choose_spec
  refine ⟨B,C,D,fun k => SmoothScales.positive (hbpos k),hBs,hD.mono (fun _ hk => hk.1),?_⟩
  have hout := original_shadow_tendsto I hclosed a K hK hKU S c hcover (fun k => 2^k) ρ hρ
    (fun k => (D k).carrier) (fun k u => ((D k).point u,u.2)) (hD.mono (fun _ hk => hk.2))
  exact hout
end SmoothObstruction.ManifoldCoordinates

end

end OAI
