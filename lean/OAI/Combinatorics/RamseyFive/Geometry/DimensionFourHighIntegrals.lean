import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Probability.DimensionFourLowIntegrals
import OAI.Combinatorics.RamseyFive.Geometry.HighPeelExceptions
import OAI.Combinatorics.RamseyFive.Geometry.UniformHighTail

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_high_score_integrals {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b₀ τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ {A : Type} [Fintype A] (g : ℝ) (F : Finset J) (hF : F.Nonempty)
      (Flat : J→Submodule K (I→K)) (H : Finset J) (hH : H.Nonempty)
      (Hyper : J→Submodule K (I→K)) (X XH U S : Finset (ℙ K (I→K)))
      (t₀ : ℝ) (ht₀ : 0<t₀) (rawOwn : ℙ K (I→K)→Finset (ℙ K (I→K)))
      (C : A→Finset (ℙ K (I→K))) (ia ib ic : ℙ K (I→K)→A),
      2<q → Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b₀ → b₀≤Cb*D*σ^(6*beta η) →
      τ≤σ^(-200*beta η) → P η σ D R/10000<g → g≤σ →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
      (X.card:ℝ)=Real.exp (2*σ+g) → (X.card:ℝ)≤10*Real.exp (5*σ/2) →
      XH=peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
        ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _) →
      t₀=(Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5) →
      S=peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀) →
      Real.exp (2*σ+g)/4≤S.card →
      (∀x,ownCell F hF (fun j=>flatPoints (Flat j)) XH
        (peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t₀⌉₊ (Nat.ceil_pos.mpr ht₀)) x⊆rawOwn x) →
      (∀x,ownCell H hH (fun j=>flatPoints (Hyper j)) X
        (peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)) x⊆rawOwn x) →
      (∀x,S∩rawOwn x=C (ia x)∪C (ib x)) →
      (∑j,(C j).card)≤3*S.card → (∀j,C j⊆S) →
      (∀x,C (ic x)=C (ia x)∩C (ib x)) →
      (Nat.card K:ℝ)/S.card≤1/100 → (∀x,ownFraction S (C (ia x)) (C (ib x))≤2/25) →
      let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
      let O := fun x => C (ia x)∪C (ib x)
      let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
      let t := scale (K:=K) 4 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
      (∫ω,((typicalFailures S S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) ∧
      (∫ω,((typicalFailures U S O (exceptional S C) ctr t ω).card:ℝ) ∂μ)≤
        (S.card:ℝ)*Real.exp (8*P η σ D R) := by
  have ht := eventually_validation_original_tail hη hη' Cb hCb
  have hu := eventually_high_original_tail_retained hη hη' Cb hCb
  have he := eventually_high_peel_exceptions hη hη'
  have heS := eventually_literal_plane_half_exceptions hη hη'
  have htr := eventually_literal_plane_global_trunc hη hη'
  have hm := eventually_score_margins hη hη' Cb hCb
  have hl := eventually_hierarchy hη hη' Cb 1 10000000000 hCb (by norm_num)
  have hc := eventually_power_absorption hη hη' (34359738369*2^200) 0 (1/200) (by positivity) (by norm_num) (by norm_num)
  have hc' := eventually_power_absorption hη hη' 33554432 0 (1/10000) (by norm_num) (by norm_num) (by norm_num)
  have hd := eventually_dyad_power_payment hη hη'
  filter_upwards [eventually_ge_atTop (1000:ℝ),ht,hu,he,heS,htr,hm,hl,hc,hc',hd] with σ hσ ht hu he heS htr hm hl hc hc' hd
  intro D b₀ τ R L₀ q K I J _ _ _ _ _ _ _ _ A _ g F hF Flat H hH Hyper X XH U S t₀ ht₀ rawOwn C ia ib ic
    hq hcard hσq hI hr hL hb₀ hbhi hτ hg hg' hFlat hcover hHyper hHcover hnX hori hXH htc hpeel hquarter hraw hrawH hOwn hC hCS hCc hdiv hf
  dsimp only
  let μ := scheduleMeasure (fun _ : S => L₀*pointStrength S) R
  let O := fun x => C (ia x)∪C (ib x)
  let O' := fun x => S∩rawOwn x
  let ctr := fun x => Real.exp (-(L₀:ℝ)*(1-ownFraction S (C (ia x)) (C (ib x))))
  let t := scale (K:=K) 4 S.card*Real.exp (-(b₀+8*P η σ D R*τ+Real.log 16))/10
  let Lines := radialInventory (K:=K) (V:=I→K)
  let Planes := F.image Flat
  let reg := irregular (d:=4) S C ((L₀:ℝ)/100)
  let rad := radialExceptions S O' (pointStrength S) Lines Finset.univ q X.card (P η σ D R/200)
  let pair := hyperplanePeelExceptions H hH Hyper X XH S Planes
    (peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _))
    (pointStrength S) (P η σ D R/200) Finset.univ
  let strong := ambientHalfStrongExceptions σ (P η σ D R) S O' Lines Finset.univ
  let bad := reg∪(rad∪pair)
  let E : ℙ K (I→K)→Set (Fin R→S→ℕ) := fun x =>
    {ω | Unsampled x S ω ∧ t < |pointScore S (O x) (pencil x\exceptional S C) (ctr x) ω|}
  let loss (x : ℙ K (I→K)) : ℝ := ∫ω,1-HighMoment.allTrunc R 5000 ω
    ∂batchMeasure (fun p : Fin R×RadialLine x => L₀*radialWeight x (outsideAt x S (O x)) (pointStrength S) p.2)
  have hSn0 : (0:ℝ)<S.card := (by positivity : (0:ℝ)<Real.exp (2*σ+g)/4).trans_le hquarter
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn0)
  have hn1 : (1:ℝ)≤S.card := by exact_mod_cast hS.card_pos
  have hdim : finrank K (I→K)=5 := by rw [Module.finrank_pi,hI]
  have hqσ : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hHX : XH⊆X := hXH▸peel_subset _ H hH (fun j=>flatPoints (Hyper j)) X _ _
  have hSH : S⊆XH := hpeel▸peel_subset _ F hF (fun j=>flatPoints (Flat j)) XH _ _
  have hSX : (S.card:ℝ)≤X.card := Nat.cast_le.mpr (Finset.card_le_card (hSH.trans hHX))
  have hXHn : (XH.card:ℝ)≤Real.exp (2*σ+g) := by rw [←hnX];exact Nat.cast_le.mpr (Finset.card_le_card hHX)
  have hn : (S.card:ℝ)≤10*Real.exp (5*σ/2) := hSX.trans hori
  have hcap : (X.card:ℝ)≤(Nat.card K:ℝ)^3 := by
    have hx : (10:ℝ)≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
    calc
      _≤10*Real.exp (5*σ/2) := hori
      _≤Real.exp (σ/2)*Real.exp (5*σ/2) := mul_le_mul_of_nonneg_right hx (Real.exp_nonneg _)
      _=_ := by rw [hqσ,←Real.exp_nat_mul,←Real.exp_add];congr 1;norm_num;ring
  have hSn : (S.card:ℝ)≤Real.exp (3*σ) := by
    have hh := hSX.trans hcap
    simpa only [hqσ,←Real.exp_nat_mul,Nat.cast_ofNat] using hh
  have hP0 : 0≤P η σ D R := by unfold P;rw [←hL];positivity
  have heq : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hPlanes : ∀V∈Planes,finrank K V=3 := by
    intro V hV;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hV;exact hFlat j hj
  have hPlanesAll : ∀V : Submodule K (I→K),finrank K V=3 → V∈Planes := by
    intro V hV;obtain ⟨j,hj,rfl⟩:=hcover V hV;exact Finset.mem_image.mpr ⟨j,hj,rfl⟩
  have he := he D R hr q K I J g F hF Flat H hH Hyper X XH S t₀ ht₀ rawOwn Lines Planes Finset.univ
    hq hcard hσq hI hg hg' hFlat hcover hHyper hHcover hPlanes hnX hori hXH htc hpeel hquarter
    hraw radialInventory_rank
  have hradpair : ((rad∪pair).card:ℝ)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000)/2 := by simpa only [hL] using he
  have heS := heS D R hr q K I J (g+σ/2) F hF Flat XH S t₀ ht₀ rawOwn Lines Finset.univ
    hq hcard hσq (Or.inr hI) (by linarith only [hg',hσ]) hFlat hcover (by rwa [heq]) (by rwa [heq]) hpeel (by rwa [heq]) hSn hraw radialInventory_rank
  have hstrong : (strong.card:ℝ)≤(S.card:ℝ)*Real.exp (7*P η σ D R) := heS.2
  have hhigh' : 8388608*(Nat.card K:ℝ)^2≤S.card := by
    have hc : (33554432:ℝ)≤Real.exp (P η σ D R/10000) := by
      simpa only [Real.rpow_zero,mul_one,one_div,one_mul,mul_comm (10000⁻¹:ℝ),div_eq_mul_inv] using hc' D R hr
    have hc := hc.trans (Real.exp_le_exp.mpr hg.le)
    have hne : Real.exp (2*σ+g)=(Nat.card K:ℝ)^2*Real.exp g := by
      rw [hqσ,←Real.exp_nat_mul,←Real.exp_add];norm_num
    have hquarter' := hquarter
    rw [hne] at hquarter'
    nlinarith only [mul_le_mul_of_nonneg_right hc (sq_nonneg (Nat.card K:ℝ)),hquarter']
  have hq2S : (q:ℝ)^2≤S.card := by
    rw [←hcard]
    exact (by nlinarith only [sq_nonneg (Nat.card K:ℝ)] : (Nat.card K:ℝ)^2≤8388608*(Nat.card K:ℝ)^2).trans hhigh'
  have htr := htr D R L₀ hr hL q K I J g F hF Flat XH S t₀ ht₀ rawOwn Lines U
    hq hcard hσq hI hg.le hg' hFlat hcover hXHn htc hpeel hquarter hq2S hraw radialInventory_rank (fun x _=>mem_radialInventory x)
  have hloss : (∑x∈U,loss x)≤Real.exp (2*σ) := by
    rw [←Finset.sum_coe_sort U]
    simpa only [loss,O,hOwn] using htr
  have hloss0 (x : ℙ K (I→K)) : 0≤loss x := by
    apply integral_nonneg
    intro ω
    exact sub_nonneg.mpr ((HighMoment.allTrunc_range R 5000 ω).2)
  have hlarge : 10000000000≤(L₀:ℝ) := by rw [hL];exact (hl D R b₀ τ hr hbhi hτ).1
  have hLP : 100*(L₀:ℝ)≤P η σ D R := by rw [hL];exact (hm D b₀ τ R hr hb₀ hbhi hτ).2.2.2.1
  have hRetained : (Nat.card K:ℝ)^2*Real.exp (P η σ D R/20000)≤S.card := by
    have hc : (4:ℝ)≤Real.exp (P η σ D R/20000) := by
      linarith only [Real.add_one_le_exp (P η σ D R/20000),hLP,hlarge]
    have he : Real.exp (P η σ D R/20000)*4≤Real.exp g := by
      calc
        _≤Real.exp (P η σ D R/20000)*Real.exp (P η σ D R/20000) := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
        _=Real.exp (P η σ D R/10000) := by rw [←Real.exp_add];congr 1;ring
        _≤Real.exp g := Real.exp_le_exp.mpr hg.le
    have hne : Real.exp (2*σ+g)=(Nat.card K:ℝ)^2*Real.exp g := by
      rw [hqσ,←Real.exp_nat_mul,←Real.exp_add];norm_num
    have hr := hquarter
    rw [hne] at hr
    nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg (Nat.card K:ℝ)),hr]
  have hreg := irregular_card_bound (d:=4) hdim (by norm_num) S C hS hC
    (ξ:=(L₀:ℝ)/100) (by linarith only [Real.add_one_le_exp ((L₀:ℝ)/100),hlarge])
  have hbad : (bad.card:ℝ)≤200000*(S.card:ℝ)*Real.exp (-2*((L₀:ℝ)/100))+
      (S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000)/2 := by
    exact (Nat.cast_le.mpr (Finset.card_union_le reg (rad∪pair)) |>.trans (by norm_cast)).trans (add_le_add hreg hradpair)
  have hpay : (bad.card:ℝ)+S.card*Real.exp (-P η σ D R/2)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) := by
    have hh := mul_le_mul_of_nonneg_left (ScoreScalars.regular_training_payment_half hlarge hLP) hSn0.le
    nlinarith only [hh,hbad]
  have hbelow (x : ℙ K (I→K)) (H : ℙ K (Dual K (I→K))) (hH : H∈pencil x\exceptional S C) :
      Incident x H ∧ H∉exceptional S C := by
    have hh := Finset.mem_sdiff.mp hH
    exact ⟨(Finset.mem_filter.mp hh.1).2,hh.2⟩
  have hgood (x : ℙ K (I→K)) (hx : x∉bad) : x∉reg ∧ x∉rad ∧ x∉pair := by
    simp only [bad,Finset.mem_union,not_or] at hx
    exact hx
  have hout (x : ℙ K (I→K)) : outsideAt x S (rawOwn x)=outsideAt x S (O x) := by
    rw [←outsideAt_clip,hOwn x]
  have hscale : (X.card:ℝ)*(pointStrength (K:=K) S:ℝ)≤4*Nat.card K := by
    rw [coe_pointStrength,←mul_div_assoc]
    apply (div_le_iff₀ hSn0).mpr
    rw [hnX]
    nlinarith only [mul_le_mul_of_nonneg_right hquarter (Nat.cast_nonneg (Nat.card K) : (0:ℝ)≤Nat.card K)]
  have hχ : (34359738369*2^200:ℝ)≤Real.exp (P η σ D R/200) := by
    simpa only [Real.rpow_zero,mul_one,one_div,one_mul,mul_comm (200⁻¹:ℝ),div_eq_mul_inv] using hc D R hr
  have hmoment (x : ℙ K (I→K)) (hx : x∉bad) :
      (∑z : DistinctPairs ↥(pencil x\exceptional S C),strength (pencilLines x (pencil x\exceptional S C))
        (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
      dyadFactor (outsideAt x S (O x)).card (P η σ D R/200)*(geometryScale (Nat.card K) S.card)^2 := by
    have hmarg (V : ↥(pencil x\exceptional S C)) :
        mass (radialWeight x (outsideAt x S (rawOwn x)) (pointStrength S))
          (pencilLines x (pencil x\exceptional S C) V)≤2 := by
      rw [hout x]
      exact (actual_radial_mass_bounds x S C hS (ia x) (ib x) (ic x) (hCS _) (hCS _) (hCc x)
        (pencil x\exceptional S C) (hbelow x) (hf x) hdiv V).2.2.trans (by norm_num)
    have hgoodrad : x∉radialExceptions S rawOwn (pointStrength S) Lines Finset.univ (Nat.card K) X.card (P η σ D R/200) := by
      simpa only [rad,hcard,radialExceptions_clip,O'] using (hgood x hx).2.1
    have hh := literal_hyperplane_pair_moment hdim H hH Hyper X XH S rawOwn Planes hPlanes hPlanesAll
      (P η σ D R/10000<g) hg hXH hSH x (hrawH x) (pencil x\exceptional S C)
      (fun V hV=>(hbelow x V hV).1) (P η σ D R/200) hχ hcap hscale hhigh' Lines (mem_radialInventory x)
      Finset.univ (Finset.mem_univ _) hmarg hgoodrad (hgood x hx).2.2
    simpa only [hout x] using hh
  have htraining (x : ℙ K (I→K)) (hx : x∉bad) : μ.real (E x)≤Real.exp (-P η σ D R/2) := by
    have hpx := hmoment x hx
    have hcard : ((outsideAt x S (O x)).card:ℝ)≤Real.exp (3*σ) :=
      (Nat.cast_le.mpr (outsideAt_card_le x S (O x))).trans hSn
    have hpay := hd D R (P η σ D R/200) (outsideAt x S (O x)).card hr (le_refl _) hcard
    have hpx' : (∑z : DistinctPairs ↥(pencil x\exceptional S C),strength (pencilLines x (pencil x\exceptional S C))
        (radialWeight x (outsideAt x S (O x)) (pointStrength S)) z^200)≤
        (scale (K:=K) 4 S.card)^2*Real.exp (P η σ D R/50) := by
      apply hpx.trans
      simpa only [dyadFactor,geometryScale,scale,mul_comm] using
        mul_le_mul_of_nonneg_right hpay (sq_nonneg ((Nat.card K:ℝ)^4/S.card))
    have hpairs (u : ℝ) (hu : 0<u) (_hu2 : u≤2) :=
      validation_pairs_from_power x (outsideAt x S (O x)) (pointStrength S) (pencil x\exceptional S C) 200 _ hpx' u hu
    exact ht 4 D b₀ τ R L₀ K (I→K) x S C (ia x) (ib x) (ic x) (pencil x\exceptional S C) t
      hdim (by norm_num) (by norm_num) hqσ hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x)
      (by convert hn using 1; norm_num) hdiv (hf x) (hbelow x) (hgood x hx).1 hpairs (le_refl _)
  have hambient (x : ℙ K (I→K)) (hx : x∉bad∪strong) : μ.real (E x)≤(Nat.card K:ℝ)^(-(50:ℝ))+loss x := by
    have hh : x∉bad ∧ x∉strong := ⟨fun h=>hx (Finset.mem_union_left _ h),fun h=>hx (Finset.mem_union_right _ h)⟩
    have hrad : x∉radialExceptions S O' (pointStrength S) Lines Finset.univ (Nat.card K) S.card (P η σ D R/100) := by
      intro hx
      apply (hgood x hh.1).2.1
      have hx := radialExceptions_chi_mono S O' (pointStrength S) Lines Finset.univ (Nat.card K) S.card
        (P η σ D R/200) (P η σ D R/100) (by linarith only [hP0]) hx
      have hx := radialExceptions_normalization S O' (pointStrength S) Lines Finset.univ (Nat.card K)
        (P η σ D R/200) S.card X.card hSn0 hSX hx
      simpa only [hcard] using hx
    apply hu D b₀ τ R L₀ K (I→K) x S C (ia x) (ib x) (ic x) (pencil x\exceptional S C) t
      hdim hqσ hr hL hb₀ hbhi hτ hS (hCS _) (hCS _) (hCc x) hn hRetained hdiv (hf x) (hbelow x)
      (hgood x hh.1).1 Lines Finset.univ (mem_radialInventory x) (Finset.mem_univ _) _ _ _ (le_refl _)
    · intro i hi hxi
      have hnot := off_radialExceptions S O' (pointStrength S) Lines Finset.univ (Nat.card K) S.card (P η σ D R/100) x hrad i
        (by simpa only [O',hOwn x] using hi)
      exact hnot ((mem_badCenters_own_congr S O' (fun _=>C (ia x)∪C (ib x)) _ _ Lines Finset.univ _ x (hOwn x)).mpr hxi)
    · apply (hmoment x hh.1).trans
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      unfold dyadFactor
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hP0])) (by positivity)
    · have hs := off_ambientHalfStrongExceptions σ (P η σ D R) S O' Lines Finset.univ x hh.2
      have hnot := hs.resolve_right (by
        intro hs
        have hq0 : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
        have hexp : Real.exp (-4*P η σ D R)<Real.exp (P η σ D R/20000) :=
          Real.exp_lt_exp.mpr (by linarith only [hLP,hlarge])
        exact (not_le_of_gt (mul_lt_mul_of_pos_left hexp (sq_pos_of_pos hq0))) (hRetained.trans hs))
      intro hx
      exact hnot ((mem_badCenters_own_congr S O' (fun _=>C (ia x)∪C (ib x)) _ _ Lines Finset.univ _ x (hOwn x)).mpr hx)
  constructor
  · have hh := integral_filter_card_le μ S bad E (Real.exp_nonneg _) (fun x hx => htraining x (Finset.mem_sdiff.mp hx).2)
    change (∫ω,((S.filter fun x=>ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans ?_ hpay
    convert hh using 1; try rfl
    apply integral_congr_ae
    filter_upwards with ω
    congr 2
    ext x
    simp only [Finset.mem_filter]
  · have hh := expected_failureCount_le μ U (bad∪strong) (fun x ω=>ω∈E x) loss (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun x _=>hloss0 x) (fun x hx=>by simpa only [Set.ofPred_mem_eq] using hambient x (Finset.mem_sdiff.mp hx).2)
    change (∫ω,((U.filter fun x=>ω∈E x).card:ℝ) ∂μ)≤_
    refine le_trans (b:=((bad∪strong).card:ℝ)+U.card*(Nat.card K:ℝ)^(-(50:ℝ))+∑x∈U,loss x) ?_ ?_
    · convert hh using 1; try rfl
      apply integral_congr_ae
      filter_upwards with ω
      unfold failureCount
      congr 2
      ext x
      simp only [Finset.mem_filter]
    have hU : (U.card:ℝ)≤2*Real.exp (4*σ) := by
      have hh := (Finset.card_le_univ U).trans (projective_card_le_two_pow hdim (by rw [hcard];omega))
      have hh : (U.card:ℝ)≤2*(Nat.card K:ℝ)^4 := by exact_mod_cast hh
      simpa only [hqσ,←Real.exp_nat_mul,Nat.cast_ofNat] using hh
    have hu : (U.card:ℝ)*(Nat.card K:ℝ)^(-(50:ℝ))≤1/2 := by
      rw [hqσ]
      exact (mul_le_mul_of_nonneg_right hU (by positivity)).trans (ScoreScalars.ambient_four_payment (by linarith only [hσ]))
    have hbadn : (bad.card:ℝ)≤S.card := by
      have hexp : Real.exp (-(L₀:ℝ)/1000)≤1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L₀.coe_nonneg) (by norm_num))
      have htpos : 0≤(S.card:ℝ)*Real.exp (-P η σ D R/2) := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
      have hb : (bad.card:ℝ)≤(S.card:ℝ)*Real.exp (-(L₀:ℝ)/1000) := by linarith only [hpay,htpos]
      exact hb.trans (mul_le_of_le_one_right hSn0.le hexp)
    have hPexp : (4:ℝ)≤Real.exp (P η σ D R) := by linarith only [Real.add_one_le_exp (P η σ D R),hLP,hlarge]
    have hexp7 : (1:ℝ)≤Real.exp (7*P η σ D R) := Real.one_le_exp (mul_nonneg (by norm_num) hP0)
    have hbadall : ((bad∪strong).card:ℝ)≤(S.card:ℝ)+(S.card:ℝ)*Real.exp (7*P η σ D R) := by
      have hc : ((bad∪strong).card:ℝ)≤(bad.card:ℝ)+strong.card := by exact_mod_cast Finset.card_union_le bad strong
      exact hc.trans (add_le_add hbadn hstrong)
    have hlossn : (∑x∈U,loss x)≤S.card := by
      apply hloss.trans
      rw [←show (q:ℝ)^2=Real.exp (2*σ) by rw [←hσq,←Real.exp_nat_mul];norm_num]
      exact hq2S
    calc
      _≤(S.card:ℝ)+(S.card:ℝ)*Real.exp (7*P η σ D R)+1/2+(S.card:ℝ) := add_le_add (add_le_add hbadall hu) hlossn
      _≤4*(S.card:ℝ)*Real.exp (7*P η σ D R) := by
        nlinarith only [mul_le_mul_of_nonneg_left hexp7 hSn0.le,hn1]
      _≤Real.exp (P η σ D R)*(S.card:ℝ)*Real.exp (7*P η σ D R) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPexp (Nat.cast_nonneg _)) (Real.exp_nonneg _)
      _=_ := by rw [mul_assoc,mul_left_comm (Real.exp _),←Real.exp_add];congr 2;ring
end SharpRamseyFive.ScoreGeometry

end OAI
