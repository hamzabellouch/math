import Mathlib
import OAI.Probability.ThorpRouting.Adaptive.TupleKernel

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.Casimir
open scoped BigOperators Classical
open Filter UnitaryFinite

lemma trace_power_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (A : V →L[ℂ] V) (hA : IsSelfAdjoint A) (r : ℕ) :
    (((LinearMap.trace ℂ V (A^r).toLinearMap).re : ℝ):ℂ) =
      LinearMap.trace ℂ V (A^r).toLinearMap := trace_real _ (hA.pow r)

lemma traceMoment_real (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (r : ℕ) :
    (traceMoment d μ e r:ℂ) =
      LinearMap.trace ℂ (Specht.hilbertSpace μ) ((K d μ e)^r).toLinearMap := by
  exact trace_power_real (V:=Specht.hilbertSpace μ) _ (K_selfadjoint d μ e) r

theorem casimir_main : MainStatement := by
  obtain ⟨a,ha,hnorm⟩ := level_contraction
  refine ⟨a,1+64*(1+heightDecay 1),ha,by linarith [heightDecay_nonneg 1],?_,?_,?_⟩
  · intro d k _ hk x
    exact density_bound d k hk x
  · intro d μ e hk
    exact ⟨hnorm d μ e hk,trace_bound d μ e⟩
  · obtain ⟨l,hl,hm⟩ := physical_convergence
    refine ⟨l,hl,fun starts => ?_⟩
    simpa only [fromDistance_eq] using hm

end Thorp.Casimir

namespace Thorp.StrongTail
open scoped BigOperators Classical
open Specht UnitaryFinite

def MainStatement : Prop :=
  ∃ p Cdensity C : ℝ, 1 < p ∧ p ≤ 2 ∧ DensityAt p Cdensity ∧
    ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool),
      ‖SparseContact.sweepOperator d μ e rev‖^2 ≤
       Real.exp (C*(μ.card-μ.rowLen 0 : ℕ)) *
       (Module.finrank ℂ (Specht.space (tailDiagram μ)):ℝ)^(-((p-1)/p))

lemma dimension_le_factorial (μ : YoungDiagram) :
    Module.finrank ℂ (space μ) ≤ μ.card.factorial := by
  have hdim : Module.finrank ℂ (space μ) ≤ Fintype.card (Tabloid μ) := by
    simpa using Submodule.finrank_le (space μ)
  have hrow : 1 ≤ Fintype.card (rowGroup μ) := Fintype.card_pos
  have hc := card_tabloid_mul_row μ
  nlinarith

lemma tail_card_exact (μ : YoungDiagram) :
    (tailDiagram μ).card = μ.card - μ.rowLen 0 := by
  rw [←card_cell,Fintype.card_congr (tailCellEquiv μ),tail_card]

lemma tail_dimension_le_factorial (μ : YoungDiagram) :
    Module.finrank ℂ (space (tailDiagram μ)) ≤ (μ.card - μ.rowLen 0).factorial := by
  simpa only [tail_card_exact] using dimension_le_factorial (tailDiagram μ)

lemma sweep_sq_palindrome (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ) (rev : Bool) :
    ‖SparseContact.sweepOperator d μ e rev‖^2 =
      ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ := by
  rw [SparseContact.sweep_forward_norm, sampleOperator_palindrome _ _ (relabelledUnitary_unitary μ e)]
  change ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))‖^2 = _
  rw [show (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint =
    star (sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e)
    (fun ω => butterflyPerm d (decodeButterfly d ω))) from rfl]
  simpa only [pow_two] using (CStarRing.norm_self_mul_star (x := sampleOperator (V := hilbertSpace μ)
    (relabelledUnitary μ e) (fun ω => butterflyPerm d (decodeButterfly d ω)))).symm

lemma sweep_sq_le_one (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ) (rev : Bool) :
    ‖SparseContact.sweepOperator d μ e rev‖^2 ≤ 1 := by
  have h := SparseContact.sweep_norm_le_one d μ e rev
  nlinarith [norm_nonneg (SparseContact.sweepOperator d μ e rev)]

theorem strong_tail : MainStatement := by
  obtain ⟨a,h,ha,hh,dE⟩ := Specht.spectral_regimes
  obtain ⟨D0,hD0⟩ := Filter.eventually_atTop.mp dE
  let d0 := max D0 1
  let t : ℝ := min a (1/1000)
  have ht : 0 < t := lt_min ha (by norm_num)
  have hta : t ≤ a := min_le_left _ _
  have htq : t ≤ 1/1000 := min_le_right _ _
  let b := t/(1+t)
  have hden : 0 < 1+t := by linarith
  have hb : 0 < b := div_pos ht hden
  have hbt : b ≤ t := (div_le_iff₀ hden).mpr (by nlinarith [sq_nonneg t])
  have hba : b ≤ a := hbt.trans hta
  have hb1 : b ≤ 1 := (div_le_one hden).mpr (by linarith)
  let C := Real.log (((2^d0).factorial:ℕ):ℝ)
  have hC : 0 ≤ C := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (2^d0))
  refine ⟨1+t,3+heightDecay 1,C,by linarith,by linarith,
    density_at_small_exponent (by linarith) (by linarith),?_⟩
  intro d μ e rev
  let k := μ.card - μ.rowLen 0
  let D : ℝ := Module.finrank ℂ (space (tailDiagram μ))
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast dimension_pos (tailDiagram μ)
  have hDp : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have hμ : μ.card=2^d := by rw [←card_cell,←Fintype.card_congr e,card_positions]
  have hform : -(((1+t)-1)/(1+t)) = -b := by dsimp [b]; congr 1; ring
  rw [hform]
  change ‖SparseContact.sweepOperator d μ e rev‖^2 ≤ Real.exp (C*k)*D^(-b)
  rw [Real.rpow_def_of_pos hDp,←Real.exp_add]
  by_cases hk : k=0
  · have hDone : D=1 := by
      have hn := tail_dimension_le_factorial μ
      change Module.finrank ℂ (space (tailDiagram μ)) ≤ k.factorial at hn
      rw [hk,Nat.factorial_zero] at hn
      have hu : D ≤ 1 := by dsimp [D]; exact_mod_cast hn
      linarith
    rw [hk,Nat.cast_zero,mul_zero,hDone,Real.log_one,zero_mul,add_zero,Real.exp_zero]
    exact sweep_sq_le_one d μ e rev
  · have hkpos : 0<k := by omega
    by_cases hd : d0 ≤ d
    · have hdpos : 0<d := by have := le_max_right D0 1; omega
      by_cases htall : (μ.card:ℝ)/2 < μ.colLen 0
      · rw [sweep_sq_palindrome,Specht.palindrome_tall_zero_general d hdpos μ e htall,
          @norm_zero (hilbertSpace μ →L[ℂ] hilbertSpace μ) _]
        exact (Real.exp_pos _).le
      · have hg := (hD0 d ((le_max_left _ _).trans hd) μ e hkpos (le_of_not_gt htall)).1
        have hrootpos : (0:ℝ)<Module.finrank ℂ (space μ) := by exact_mod_cast dimension_pos μ
        have hlogle : Real.log D ≤ Real.log (Module.finrank ℂ (space μ):ℝ) :=
          Real.log_le_log hDp (by dsimp [D]; exact_mod_cast tail_dimension_le μ)
        rw [sweep_sq_palindrome]
        apply hg.trans
        apply Real.exp_le_exp.mpr
        have hbound := mul_le_mul hba hlogle hlog ha.le
        have hck : 0 ≤ C*(k:ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
        nlinarith
    · have hpow : 2^d ≤ 2^d0 := Nat.pow_le_pow_right (by decide) (by omega)
      have hklarge : k ≤ 2^d0 := (by simp [k,hμ] : k ≤ 2^d).trans hpow
      have hdim : D ≤ ((2^d0).factorial:ℝ) := by
        dsimp [D]
        exact_mod_cast (tail_dimension_le_factorial μ).trans (Nat.factorial_le hklarge)
      have hlC : Real.log D ≤ C := Real.log_le_log hDp hdim
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hkpos
      have hprod : b*Real.log D ≤ C*(k:ℝ) := by nlinarith
      apply (sweep_sq_le_one d μ e rev).trans
      exact Real.one_le_exp_iff.mpr (by nlinarith)

end Thorp.StrongTail

namespace Thorp.Harmonic
open scoped BigOperators Classical

section
open Casimir StrongSmoothing

abbrev tail (μ : YoungDiagram) := StrongTail.tailDiagram μ
noncomputable def W (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) : ℝ := ‖K d μ e‖
noncomputable def tupleTrace (d k : ℕ) (order : Equiv.Perm (Fin d)) (rev : Bool) (p : ℕ) : ℝ :=
  Matrix.trace ((reflectedKernel d k order rev)^p)

def MainStatement : Prop :=
  ∃ c C ζ δ cTail c₁ c₂ : ℝ, ∃ p₀ : ℕ,
    0<c ∧ 0<C ∧ 0<ζ ∧ 0<δ ∧ δ<1 ∧ 0<cTail ∧ 0<c₁ ∧ 0<c₂ ∧ 0<p₀ ∧
    (∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0<μ.card-μ.rowLen 0 →
      let L := levelScale (2^d) (μ.card-μ.rowLen 0)
      let f : ℝ := Module.finrank ℂ (Specht.space (tail μ))
      let D : ℝ := Module.finrank ℂ (Specht.space μ)
      W d μ e ≤ Real.exp (-c*L) ∧
      W d μ e ≤ Real.exp (C*L)*f^(-ζ) ∧
      (∀ rev : Bool, ‖SparseContact.sweepOperator d μ e rev‖ ≤
        Real.exp (-cTail*(L+Real.log f))) ∧
      W d μ e ≤ Real.exp (-c₁*L)*D^(-c₂)) ∧
    (∀ d k : ℕ, 1≤k → k≤2^d → ∀ (order : Equiv.Perm (Fin d)) (rev : Bool),
      (∀ x : Tuples d k,
        finiteMean (fun y => ((Fintype.card (Tuples d k):ℝ)*
          reflectedKernel d k order rev x y)^(1+δ)) ≤
        Real.exp (C*levelScale (2^d) k)) ∧
      tupleTrace d k order rev p₀ ≤ Real.exp (C*levelScale (2^d) k))

end
open Filter Casimir StrongSmoothing

lemma dimension_contraction :
    ∃ b : ℝ, 0<b ∧ ∀ (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ),
      0<μ.card-μ.rowLen 0 →
      W d μ e ≤ Real.exp (-b*Real.log (Module.finrank ℂ (Specht.space μ):ℝ)) := by
  obtain ⟨a,h,ha,hh,he⟩ := Specht.spectral_regimes
  obtain ⟨D,hD⟩ := eventually_atTop.mp (he.and (eventually_ge_atTop 1))
  let B (d : ℕ) : ℝ := 1+Real.log ((2^d).factorial:ℝ)
  have hB (d : ℕ) : 0<B d := by
    have hh : 0≤Real.log ((2^d).factorial:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (2^d))
    dsimp [B]; linarith
  let f (d : ℕ) : ℝ := -Real.log (blockGap d)/B d
  have hf (d : ℕ) : 0<f d :=
    div_pos (neg_pos.mpr (Real.log_neg (blockGap_pos d) (blockGap_lt_one d))) (hB d)
  obtain ⟨b,hb,hbD⟩ := finite_positive_lower f D (fun d _ => hf d)
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro d μ e hk
  have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hDpos : (0:ℝ)<Module.finrank ℂ (Specht.space μ) := by exact_mod_cast Specht.dimension_pos μ
  have hL : 0≤Real.log (Module.finrank ℂ (Specht.space μ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast Specht.dimension_pos μ)
  by_cases hd : D≤d
  · obtain ⟨hs,hd1⟩ := hD d hd
    by_cases ht : (μ.card:ℝ)/2<μ.colLen 0
    · have hz := Specht.palindrome_tall_zero_general d (by omega) μ e ht
      change K d μ e=0 at hz
      change ‖K d μ e‖≤_
      rw [hz,@norm_zero (Specht.hilbertSpace μ →L[ℂ] Specht.hilbertSpace μ) _]
      exact (Real.exp_pos _).le
    · apply (hs μ e hk (le_of_not_gt ht)).1.trans
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (min_le_left a b) hL
      linarith
  · have hdim : Real.log (Module.finrank ℂ (Specht.space μ):ℝ) ≤ B d := by
      have hh := StrongTail.dimension_le_factorial μ
      rw [hμ] at hh
      have hl := Real.log_le_log hDpos (show (Module.finrank ℂ (Specht.space μ):ℝ)≤(2^d).factorial by exact_mod_cast hh)
      dsimp [B]; linarith
    have hab : min a b≤f d := (min_le_right _ _).trans (hbD d (by omega))
    have hp := mul_le_mul_of_nonneg_right hab (hB d).le
    have heq : f d*B d = -Real.log (blockGap d) := by dsimp [f]; field_simp [ne_of_gt (hB d)]
    rw [heq] at hp
    have hscale := mul_le_mul_of_nonneg_left hdim (le_of_lt (lt_min ha hb))
    calc
      W d μ e ≤ blockGap d := nontrivial_gap d μ e hk
      _ = Real.exp (Real.log (blockGap d)) := (Real.exp_log (blockGap_pos d)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

lemma exp_intersection {x A B : ℝ} (hx : 0≤x) (hA : x≤Real.exp A) (hB : x≤Real.exp B) :
    x≤Real.exp ((A+B)/2) := by
  have hh := mul_le_mul hA hB hx (Real.exp_pos A).le
  rw [←Real.exp_add] at hh
  have he : Real.exp ((A+B)/2)^2=Real.exp (A+B) := by
    rw [pow_two,←Real.exp_add]
    congr 1; ring
  nlinarith [Real.exp_pos ((A+B)/2)]

lemma flat_tuple_trace (d k : ℕ) (hk : k≤2^d) (order : Equiv.Perm (Fin d)) (rev : Bool) :
    tupleTrace d k order rev 2001 ≤ Real.exp ((2000*(1+heightDecay 1))*k) := by
  have hpos : 0<Fintype.card (Tuples d k) := by
    rw [tuples_card]
    exact Nat.descFactorial_pos.mpr hk
  have hne : (Fintype.card (Tuples d k):ℝ)≠0 := by exact_mod_cast ne_of_gt hpos
  calc
    _ ≤ ∑ x : Tuples d k, Real.exp ((2000*(1+heightDecay 1))*k)/
        ((2^d).descFactorial k:ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact both_pointwise d k order rev x x
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←tuples_card]
      field_simp

theorem harmonic_cycle_main : MainStatement := by
  obtain ⟨a,ha,hlevel⟩ := level_contraction
  obtain ⟨b,hb,hdim⟩ := dimension_contraction
  let C : ℝ := 2000*(1+heightDecay 1)
  have hA : 0≤heightDecay 1 := heightDecay_nonneg 1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨a,C,b,1/1000,min a b/4,a/2,b/2,2001,
    ha,hC,hb,by norm_num,by norm_num,by positivity,by positivity,by positivity,by norm_num,?_,?_⟩
  · intro d μ e hk
    dsimp only
    let L := levelScale (2^d) (μ.card-μ.rowLen 0)
    let f : ℝ := Module.finrank ℂ (Specht.space (tail μ))
    let D : ℝ := Module.finrank ℂ (Specht.space μ)
    have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
    have hkn : μ.card-μ.rowLen 0≤2^d := by omega
    have hL : 0≤L := (Nat.cast_nonneg _).trans (levelScale_ge _ _ hkn)
    have hfp : 0<f := by dsimp [f,tail]; exact_mod_cast Specht.dimension_pos (StrongTail.tailDiagram μ)
    have hfl : 0≤Real.log f := Real.log_nonneg (by dsimp [f,tail]; exact_mod_cast Specht.dimension_pos (StrongTail.tailDiagram μ))
    have hDp : 0<D := by dsimp [D]; exact_mod_cast Specht.dimension_pos μ
    have hle : Real.log f≤Real.log D := Real.log_le_log hfp (by
      dsimp [f,D,tail]; exact_mod_cast StrongTail.tail_dimension_le μ)
    have hw := hlevel d μ e hk
    have hd := hdim d μ e hk
    change W d μ e≤Real.exp (-a*L) at hw
    change W d μ e≤Real.exp (-b*Real.log D) at hd
    have ht : W d μ e≤Real.exp (-b*Real.log f) := hd.trans (Real.exp_le_exp.mpr (by nlinarith))
    refine ⟨hw,?_,?_,?_⟩
    · change W d μ e≤Real.exp (C*L)*f^(-b)
      rw [Real.rpow_def_of_pos hfp,←Real.exp_add]
      exact ht.trans (Real.exp_le_exp.mpr (by nlinarith))
    · intro rev
      have hg := exp_intersection (norm_nonneg (K d μ e)) hw ht
      have hcoef : (-a*L+-b*Real.log f)/2 ≤ -2*(min a b/4)*(L+Real.log f) := by
        have h₁ := mul_le_mul_of_nonneg_right (min_le_left a b) hL
        have h₂ := mul_le_mul_of_nonneg_right (min_le_right a b) hfl
        nlinarith
      have hg' := hg.trans (Real.exp_le_exp.mpr hcoef)
      have hs := StrongTail.sweep_sq_palindrome d μ e rev
      change ‖SparseContact.sweepOperator d μ e rev‖^2=W d μ e at hs
      change W d μ e≤_ at hg'
      rw [←hs] at hg'
      have he : Real.exp (-(min a b/4)*(L+Real.log f))^2 =
          Real.exp (-2*(min a b/4)*(L+Real.log f)) := by
        rw [pow_two,←Real.exp_add]
        congr 1; ring
      change ‖SparseContact.sweepOperator d μ e rev‖≤Real.exp (-(min a b/4)*(L+Real.log f))
      nlinarith [Real.exp_pos (-(min a b/4)*(L+Real.log f))]
    · change W d μ e≤Real.exp (-(a/2)*L)*D^(-(b/2))
      rw [Real.rpow_def_of_pos hDp,←Real.exp_add]
      have hg := exp_intersection (norm_nonneg (K d μ e)) hw hd
      have he : -(a/2)*L+Real.log D*(-(b/2))=(-a*L+-b*Real.log D)/2 := by ring
      rw [he]
      exact hg
  · intro d k _ hk order rev
    have hL := levelScale_ge (2^d) k hk
    have hcoef : k*(1+heightDecay 1) ≤ C*levelScale (2^d) k := by
      have hk0 : (0:ℝ)≤k := by positivity
      dsimp [C]; nlinarith
    refine ⟨?_,?_⟩
    · intro x
      exact (StrongTail.reflected_moment_both d k order rev x).trans (Real.exp_le_exp.mpr hcoef)
    · exact (flat_tuple_trace d k hk order rev).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hC.le))

end Thorp.Harmonic


namespace Thorp.AdaptiveBounds
open scoped BigOperators Classical

def mesh : ℕ → ℕ
  | 0 => 1024
  | i+1 => mesh i + mesh i/32

def width (i : ℕ) : ℕ := mesh i/32

lemma mesh_ge (i : ℕ) : 1024 ≤ mesh i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [mesh]; omega

lemma width_ge (i : ℕ) : 32 ≤ width i := by
  unfold width
  exact (Nat.le_div_iff_mul_le (by decide)).mpr (mesh_ge i)

lemma mesh_step (i : ℕ) : mesh (i+1)=mesh i+width i := rfl

lemma mesh_lower (i : ℕ) : 1024+32*i ≤ mesh i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [mesh_step]; have hh:=width_ge i; omega

lemma width_lower (i : ℕ) : 32+i ≤ width i := by
  unfold width
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  have hh := mesh_lower i
  omega

lemma width_pos (i : ℕ) : 0<width i := by have := width_ge i; omega

lemma mesh_monotone : Monotone mesh := by
  apply monotone_nat_of_le_succ
  intro i
  rw [mesh_step]
  omega

lemma mesh_strictMono : StrictMono mesh := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [mesh_step]
  have :=width_pos i
  omega

lemma width_le (i : ℕ) : 32*width i ≤ mesh i := by
  exact Nat.mul_div_le (mesh i) 32

lemma mesh_growth (i : ℕ) : (1055/1024:ℝ)*mesh i ≤ mesh (i+1) := by
  have hm : (1024:ℝ)≤ mesh i := by exact_mod_cast mesh_ge i
  have hw : (mesh i:ℝ)<32*((width i:ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ (mesh i) (by decide : 0<32)
  rw [mesh_step,Nat.cast_add]
  nlinarith

lemma mesh_growth_iter (i j : ℕ) : (1055/1024:ℝ)^j*mesh i ≤ mesh (i+j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ht := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ)≤1055/1024)
    have hn :=mesh_growth (i+j)
    rw [pow_succ]
    have he : i+(j+1)=i+j+1 := by omega
    rw [he]
    nlinarith

lemma mesh_seven (i : ℕ) : 16*mesh i ≤ 13*mesh (i+7) := by
  have hh := mesh_growth_iter i 7
  have hn : (0:ℝ)≤ mesh i := by positivity
  have hc : (16/13:ℝ)≤(1055/1024:ℝ)^7 := by norm_num
  have ht:=mul_le_mul_of_nonneg_right hc hn
  have hl : (16:ℝ)*mesh i ≤13*mesh (i+7) := by linarith
  exact_mod_cast hl

lemma mesh_fresh (i : ℕ) : 6*width (i+8)+mesh (i+1) ≤ mesh (i+8) := by
  have hs :=mesh_seven (i+1)
  have hw :=width_le (i+8)
  have he : i+1+7=i+8 := by omega
  rw [he] at hs
  omega

lemma mesh_fresh_first (i : ℕ) : 6*width i ≤ mesh i := by
  have :=width_le i
  omega


lemma coefficient_decay (w r : ℕ) (hr : 6*w ≤ r)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ (8*(w:ℝ)/3)*Real.log 2) :
    cycleCoefficient r ⌈Real.exp ((w:ℝ)/32)⌉₊ q ≤
      196*Real.exp (-(w:ℝ)/64) := by
  let E := Real.exp ((w:ℝ)/32)
  let J := ⌈E⌉₊
  have hw : (0:ℝ) ≤ w := Nat.cast_nonneg _
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hEp : 0<E := Real.exp_pos _
  have hEJ : E ≤ (J:ℝ) := Nat.le_ceil E
  have hJ : (1:ℝ) ≤ J := hE.trans hEJ
  have hJE : (J:ℝ) ≤ 2*E := by
    have hh := Nat.ceil_lt_add_one hEp.le
    change (J:ℝ)<E+1 at hh
    linarith
  have hsJ : Real.sqrt J ≤ (J:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hqp : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hqE : q ≤ Real.exp ((8*(w:ℝ)/3)*Real.log 2) := by
    rw [←Real.exp_log hqp]
    exact Real.exp_le_exp.mpr hlog
  have hln0 : (0:ℝ)≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hln : (1/2:ℝ)≤Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hln1 : Real.log 2 ≤ 1 := by
    have hh :=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hden : Real.exp (3*(w:ℝ)*Real.log 2) ≤ Real.sqrt ((2:ℝ)^r) := by
    have he : (2:ℝ)^r=Real.exp ((r:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    rw [he,Real.sqrt_eq_rpow,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    apply Real.exp_le_exp.mpr
    have hrr : (6:ℝ)*w ≤ r := by exact_mod_cast hr
    nlinarith
  have hlog' : Real.log q ≤ 3*(w:ℝ) := by nlinarith
  have h₁ : Real.log q/(J:ℝ) ≤ 192*Real.exp (-(w:ℝ)/64) := by
    calc
      _ ≤ (3*(w:ℝ))/E := div_le_div₀ (by positivity) hlog' hEp hEJ
      _ ≤ (192*Real.exp ((w:ℝ)/64))/E := by
        apply div_le_div_of_nonneg_right _ hEp.le
        have hh :=Real.add_one_le_exp ((w:ℝ)/64)
        linarith
      _ = _ := by
        dsimp [E]
        rw [mul_div_assoc,←Real.exp_sub]
        congr 2
        ring
  have h₂ : 2*q*Real.sqrt J/Real.sqrt ((2:ℝ)^r) ≤
      4*Real.exp (-(w:ℝ)/64) := by
    calc
      _ ≤ (4*Real.exp ((8*(w:ℝ)/3)*Real.log 2)*E)/
          Real.exp (3*(w:ℝ)*Real.log 2) := by
        apply div_le_div₀ (by positivity) _ (Real.exp_pos _) hden
        have hm :=mul_le_mul hqE (hsJ.trans hJE) (Real.sqrt_nonneg _) (Real.exp_nonneg _)
        nlinarith
      _ = 4*Real.exp ((8*(w:ℝ)/3)*Real.log 2+(w:ℝ)/32-3*(w:ℝ)*Real.log 2) := by
        dsimp [E]
        rw [mul_assoc,←Real.exp_add,mul_div_assoc,←Real.exp_sub]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
        nlinarith
  change Real.log q/(J:ℝ)+2*q*Real.sqrt J/Real.sqrt ((2:ℝ)^r) ≤ _
  linarith

noncomputable def bandCost (a w d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ i : Fin w, palindromeLevelCost (a+i.1+1) d e ω

lemma band_adapted (a w d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (a+w) (fun Y => bandCost a w d e (Y,X)) := by
  apply layerAdapted_sum
  intro i _
  exact layerAdapted_mono (palindromeLevelCost_adapted (a+i.1+1) d e X) (by omega)

lemma band_gt (a w d : ℕ) (hd : d ≤ a) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : bandCost a w d e ω=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact palindromeLevelCost_gt _ _ (by omega) _ _

lemma band_partial_mgf (r s a w : ℕ) (hw : 0<w) (hs : 6*w+s ≤ a)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card (s+r)) (X : SwitchIndex (s+r) → Bool)
    (lo : Card r × SwitchIndex s → Bool) (q : ℝ) (hq : 1 ≤ q)
    (hlog : Real.log q ≤ (8/3:ℝ)*Real.log 2) :
    finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
      q^(bandCost a w (s+r) e (assembleBits r s lo hi,X))) ≤
      Real.exp (Fintype.card ι*(196*Real.exp (-(w:ℝ)/64))) := by
  let : NeZero w := ⟨ne_of_gt hw⟩
  have hqp : 0<q := lt_of_lt_of_le (by norm_num) hq
  calc
    _ ≤ finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
        finiteMean (fun i : Fin w => q^(w*palindromeLevelCost (a+i.1+1) (s+r) e
          (assembleBits r s lo hi,X)))) := by
      apply finiteMean_mono
      intro hi
      simpa only [bandCost,Fintype.card_fin] using
        pow_sum_le_mean_powers (fun i : Fin w => palindromeLevelCost (a+i.1+1) (s+r) e
          (assembleBits r s lo hi,X)) q hqp
    _ = finiteMean (fun i : Fin w => finiteMean (fun hi : Card s × SwitchIndex r → Bool =>
        q^(w*palindromeLevelCost (a+i.1+1) (s+r) e (assembleBits r s lo hi,X)))) :=
      finiteMean_comm _
    _ ≤ finiteMean (fun _i : Fin w =>
        Real.exp (Fintype.card ι*(196*Real.exp (-(w:ℝ)/64)))) := by
      apply finiteMean_mono
      intro i
      by_cases ht : a+i.1+1 ≤ s+r
      · have hs' : s ≤ a+i.1 := by omega
        have he : a+i.1+1=s+(a+i.1-s)+1 := by omega
        have hu : a+i.1-s<r := by omega
        have hm :=palindrome_level_partial_mgf r s (a+i.1-s) hu e X lo
          ⌈Real.exp ((w:ℝ)/32)⌉₊ (cycleCutoff_pos w) (q^w) (one_le_pow₀ hq)
        have hc :=coefficient_decay w (a+i.1-s) (by omega) (q^w) (one_le_pow₀ hq) (by
          rw [Real.log_pow]
          have hh:=mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg w)
          nlinarith)
        simp_rw [he,pow_mul]
        exact hm.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)))
      · have hz:=palindromeLevelCost_gt (a+i.1+1) (s+r) (by omega) e
        simp only [hz,Nat.mul_zero,pow_zero,finiteMean_const]
        exact Real.one_le_exp_iff.mpr (by positivity)
    _ = _ := finiteMean_const _

lemma band_adapted_mgf (d s a w : ℕ) (hsd : s ≤ d) (hw : 0<w) (hs : 6*w+s ≤ a)
    {ι : Type*} [Fintype ι] (e : ι ↪ Card d) (X : SwitchIndex d → Bool)
    (F : (SwitchIndex d → Bool) → ℝ) (hF : ∀ Y,0 ≤ F Y) (hA : LayerAdapted d s F)
    (q : ℝ) (hq : 1 ≤ q) (hlog : Real.log q ≤ (8/3:ℝ)*Real.log 2) :
    finiteMean (fun Y => F Y*q^(bandCost a w d e (Y,X))) ≤
      finiteMean F *Real.exp (Fintype.card ι*(196*Real.exp (-(w:ℝ)/64))) := by
  obtain ⟨r,rfl⟩ :=Nat.exists_eq_add_of_le hsd
  exact adapted_mul_mean_le r s F _ hF hA _
    (fun lo => band_partial_mgf r s a w hw hs e X lo q hq hlog)


def bandEnd (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => mesh (8*n+i+1)

lemma bandEnd_fresh (i n : ℕ) : 6*width (8*n+i)+bandEnd i n ≤ mesh (8*n+i) := by
  cases n with
  | zero => simpa [bandEnd] using mesh_fresh_first i
  | succ n =>
    have hh := mesh_fresh (8*n+i)
    simpa only [bandEnd,show 8*(n+1)+i=8*n+i+8 by omega] using hh

lemma bandEnd_ge (i n j : ℕ) (hj : j<n) : mesh (8*j+i+1) ≤ bandEnd i n := by
  cases n with
  | zero => omega
  | succ n => exact mesh_monotone (by omega)

noncomputable def familyCost (i n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) : ℕ :=
  ∑ j ∈ Finset.range n, bandCost (mesh (8*j+i)) (width (8*j+i)) d e ω

lemma family_adapted (i n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) :
    LayerAdapted d (bandEnd i n) (fun Y => familyCost i n d e (Y,X)) := by
  apply layerAdapted_sum
  intro j hj
  apply layerAdapted_mono (band_adapted _ _ _ e X)
  rw [←mesh_step]
  exact bandEnd_ge i n j (Finset.mem_range.mp hj)

lemma family_mgf (i n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1≤q)
    (hlog : Real.log q ≤ (8/3:ℝ)*Real.log 2) :
    finiteMean (fun Y => q^(familyCost i n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*(196*∑ j ∈ Finset.range n,
        Real.exp (-(width (8*j+i):ℝ)/64))) := by
  induction n with
  | zero => simp only [familyCost,Finset.range_zero,Finset.sum_empty,pow_zero,
      finiteMean_const,mul_zero,Real.exp_zero,le_refl]
  | succ n ih =>
    let a := mesh (8*n+i)
    let w := width (8*n+i)
    have hw : 0<w := width_pos _
    have hs : 6*w+bandEnd i n ≤ a := bandEnd_fresh i n
    have hc (Y) : familyCost i (n+1) d e (Y,X)=familyCost i n d e (Y,X)+
        bandCost a w d e (Y,X) := Finset.sum_range_succ _ _
    have hm : finiteMean (fun Y => q^(familyCost i (n+1) d e (Y,X))) ≤
        finiteMean (fun Y => q^(familyCost i n d e (Y,X)))*
          Real.exp (Fintype.card ι*(196*Real.exp (-(w:ℝ)/64))) := by
      by_cases had : a ≤ d
      · simp_rw [hc,pow_add]
        exact band_adapted_mgf d (bandEnd i n) a w (by omega) hw hs e X _
          (fun _ => pow_nonneg (by linarith) _)
          (layerAdapted_comp (family_adapted i n d e X) (fun c => q^c)) q hq hlog
      · simp_rw [hc,band_gt a w d (by omega) e,Nat.add_zero]
        exact le_mul_of_one_le_right
          (finiteMean_nonneg (fun _ => pow_nonneg (by linarith) _))
          (Real.one_le_exp_iff.mpr (by positivity))
    refine (hm.trans (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _))).trans_eq ?_
    rw [←Real.exp_add,Finset.sum_range_succ]
    congr 1
    dsimp [w]
    ring

noncomputable def familyBound : ℝ := 196/(1-Real.exp (-(1:ℝ)/64))

lemma familyBound_pos : 0<familyBound := by
  have hh : Real.exp (-(1:ℝ)/64)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  unfold familyBound
  positivity

lemma family_decay (i n : ℕ) :
    (∑ j ∈ Finset.range n, Real.exp (-(width (8*j+i):ℝ)/64)) ≤
      1/(1-Real.exp (-(1:ℝ)/64)) := by
  let r := Real.exp (-(1:ℝ)/64)
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hg : (∑ j ∈ Finset.range n, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<1-r)).mpr
    have hh:=geom_sum_mul r n
    nlinarith [pow_nonneg hr.le n]
  apply le_trans _ hg
  apply Finset.sum_le_sum
  intro j _
  have hw : j ≤ width (8*j+i) := by have hh:=width_lower (8*j+i); omega
  have hw' : (j:ℝ)≤width (8*j+i) := by exact_mod_cast hw
  dsimp [r]
  rw [←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  linarith

lemma family_mgf_bound (i n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1≤q)
    (hlog : Real.log q ≤ (8/3:ℝ)*Real.log 2) :
    finiteMean (fun Y => q^(familyCost i n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*familyBound) := by
  apply (family_mgf i n d e X q hq hlog).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hh:=mul_le_mul_of_nonneg_left (family_decay i n) (by norm_num : (0:ℝ)≤196)
  simpa only [familyBound,mul_one_div] using hh


lemma low_band (i d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost (mesh i) d e ω+bandCost (mesh i) (width i) d e ω=
      palindromeLowCost (mesh (i+1)) d e ω := by
  rw [mesh_step,palindromeLowCost_sum,palindromeLowCost_sum,Finset.sum_range_add]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun j => palindromeLevelCost (mesh i+j+1) d e ω) (width i)

lemma low_bands (a m d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost (mesh a) d e ω+
      (∑ i ∈ Finset.range m, bandCost (mesh (a+i)) (width (a+i)) d e ω)=
      palindromeLowCost (mesh (a+m)) d e ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,←Nat.add_assoc,ih]
    simpa only [Nat.add_assoc] using low_band (a+m) d e ω

lemma cost_families (n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (ω : BenesCoins d) :
    palindromeLowCost 1024 d e ω+(∑ i : Fin 8, familyCost i.1 n d e ω)=
      palindromeLowCost (mesh (8*n)) d e ω := by
  induction n with
  | zero => simp [familyCost,mesh]
  | succ n ih =>
    have hh := low_bands (8*n) 8 d e ω
    rw [←Fin.sum_univ_eq_sum_range] at hh
    simp only [familyCost,Finset.sum_range_succ,Finset.sum_add_distrib] at ih ⊢
    rw [←Nat.add_assoc,ih]
    convert hh using 1

lemma high_mgf (n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (X : SwitchIndex d → Bool) (q : ℝ) (hq : 1≤q)
    (hlog : Real.log q ≤ Real.log 2/3) :
    finiteMean (fun Y => q^(∑ i : Fin 8, familyCost i.1 n d e (Y,X))) ≤
      Real.exp (Fintype.card ι*familyBound) := by
  have hqp : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hl8 : Real.log (q^8) ≤ (8/3:ℝ)*Real.log 2 := by
    rw [Real.log_pow]
    norm_num
    linarith
  calc
    _ ≤ finiteMean (fun Y => finiteMean (fun i : Fin 8 => q^(8*familyCost i.1 n d e (Y,X)))) := by
      apply finiteMean_mono
      intro Y
      simpa only [Fintype.card_fin] using
        pow_sum_le_mean_powers (fun i : Fin 8 => familyCost i.1 n d e (Y,X)) q hqp
    _ = finiteMean (fun i : Fin 8 => finiteMean (fun Y => q^(8*familyCost i.1 n d e (Y,X)))) :=
      finiteMean_comm _
    _ ≤ finiteMean (fun _i : Fin 8 => Real.exp (Fintype.card ι*familyBound)) := by
      apply finiteMean_mono
      intro i
      simpa only [pow_mul] using family_mgf_bound i.1 n d e X (q^8) (one_le_pow₀ hq) hl8
    _ = _ := finiteMean_const _

lemma high_full_mgf (n d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1≤q) (hlog : Real.log q ≤ Real.log 2/3) :
    finiteMean (fun ω : BenesCoins d => q^(∑ i : Fin 8, familyCost i.1 n d e ω)) ≤
      Real.exp (Fintype.card ι*familyBound) := by
  rw [finiteMean_prod,finiteMean_comm]
  calc
    _ ≤ finiteMean (fun _X : SwitchIndex d → Bool => Real.exp (Fintype.card ι*familyBound)) :=
      finiteMean_mono (fun X => high_mgf n d e X q hq hlog)
    _ = _ := finiteMean_const _

noncomputable def densityConstant : ℝ := 1024+familyBound

lemma densityConstant_pos : 0<densityConstant := by
  dsimp [densityConstant]
  linarith [familyBound_pos]

lemma cost_mgf (d : ℕ) {ι : Type*} [Fintype ι]
    (e : ι ↪ Card d) (q : ℝ) (hq : 1≤q) (hlog : Real.log q ≤ Real.log 2/3) :
    finiteMean (fun ω : BenesCoins d => q^(palindromeCost d e ω)) ≤
      Real.exp (Fintype.card ι*densityConstant) := by
  have hd : d ≤ mesh (8*d) := by have hh:=mesh_lower (8*d); omega
  have hcost (ω : BenesCoins d) : palindromeCost d e ω=palindromeLowCost 1024 d e ω+
      (∑ i : Fin 8, familyCost i.1 d d e ω) := by
    have hh := cost_families d d e ω
    rw [palindromeLowCost_eq _ _ hd] at hh
    exact hh.symm
  have hqp : 0<q := lt_of_lt_of_le (by norm_num) hq
  have hl1 : Real.log q ≤ 1 := by
    have hh:= Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    linarith
  have hlow (ω : BenesCoins d) : q^(palindromeLowCost 1024 d e ω) ≤
      Real.exp (1024*Fintype.card ι) := by
    calc
      _ ≤ q^(1024*Fintype.card ι) := pow_le_pow_right₀ hq (palindromeLowCost_le 1024 d e ω)
      _ = Real.exp ((1024*Fintype.card ι:ℕ)*Real.log q) := by
        rw [Real.exp_nat_mul,Real.exp_log hqp]
      _ ≤ _ := Real.exp_le_exp.mpr (by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card ι)])
  calc
    _ ≤ finiteMean (fun ω : BenesCoins d => Real.exp (1024*Fintype.card ι)*
        q^(∑ i : Fin 8, familyCost i.1 d d e ω)) := by
      apply finiteMean_mono
      intro ω
      rw [hcost,pow_add]
      exact mul_le_mul_of_nonneg_right (hlow ω) (pow_nonneg hqp.le _)
    _ = Real.exp (1024*Fintype.card ι)*finiteMean (fun ω : BenesCoins d =>
        q^(∑ i : Fin 8, familyCost i.1 d d e ω)) := by
      simpa only [mul_comm] using finiteMean_mul_const
        (fun ω : BenesCoins d => q^(∑ i : Fin 8, familyCost i.1 d d e ω))
        (Real.exp (1024*Fintype.card ι))
    _ ≤ Real.exp (1024*Fintype.card ι)*Real.exp (Fintype.card ι*familyBound) :=
      mul_le_mul_of_nonneg_left (high_full_mgf d d e q hq hlog) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; dsimp [densityConstant]; congr 1; ring

lemma row_moment (d : ℕ) {ι : Type*} [Fintype ι] (e : ι ↪ Card d) :
    palindromeRowMoment d e (1/3) ≤ Real.exp (Fintype.card ι*densityConstant) := by
  let q : ℝ := (2:ℝ)^(1/3:ℝ)
  have hq : 1≤q := Real.one_le_rpow (by norm_num) (by norm_num)
  have hlog : Real.log q ≤ Real.log 2/3 := by
    dsimp [q]
    rw [Real.log_rpow (by norm_num)]
    linarith
  have hn : (0:ℝ)<((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn0 : (0:ℝ)≤((2^d).descFactorial (Fintype.card ι):ℝ)/
      ((2^d:ℕ):ℝ)^(Fintype.card ι) := by positivity
  have hn1 : ((2^d).descFactorial (Fintype.card ι):ℝ)/
      ((2^d:ℕ):ℝ)^(Fintype.card ι)≤1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.descFactorial_le_pow (2^d) (Fintype.card ι)
  have hp := Real.rpow_le_one hn0 hn1 (by norm_num : (0:ℝ)≤1/3)
  have hm := palindrome_row_density_moment d e (1/3) (by norm_num)
  have he (c : ℕ) : q^c=(2:ℝ)^((c:ℝ)*(1/3)) := by
    rw [mul_comm,Real.rpow_mul_natCast (by norm_num)]
  simp_rw [←he] at hm
  exact (hm.trans (mul_le_of_le_one_left
    (finiteMean_nonneg (fun _ => pow_nonneg (le_trans (by norm_num) hq) _)) hp)).trans
      (cost_mgf d e q hq hlog)


lemma rpow_two_thirds_sq (x : ℝ) (hx : 0≤x) : (x^(2/3:ℝ))^2=x^(4/3:ℝ) := by
  rw [←Real.rpow_mul_natCast hx]
  norm_num

lemma rpow_one_third_sq (x : ℝ) (hx : 0≤x) : (x^(1/3:ℝ))^2=x^(2/3:ℝ) := by
  rw [←Real.rpow_mul_natCast hx]
  norm_num

lemma rpow_thirds (x : ℝ) (hx : 0≤x) : x^(2/3:ℝ)*x^(1/3:ℝ)=x := by
  rw [←Real.rpow_add' hx (by norm_num : (2/3:ℝ)+1/3≠0)]
  norm_num

lemma young_cauchy {X : Type*} [Fintype X] (f g : X → ℝ)
    (hf : ∀ x,0≤f x) (hg : ∀ x,0≤g x) (M : ℝ) (hM : 0≤M)
    (hmf : finiteMean (fun x => (f x)^(4/3:ℝ))≤M)
    (hmg : finiteMean (fun x => (g x)^(4/3:ℝ))≤M) :
    (finiteMean (fun x => f x*g x))^2 ≤
      M*finiteMean (fun x => (f x)^(4/3:ℝ)*(g x)^(4/3:ℝ)) := by
  have hh := finiteMean_mul_sq_le (fun x => (f x)^(2/3:ℝ)) (fun x => (g x)^(2/3:ℝ))
  simp_rw [rpow_two_thirds_sq _ (hf _),rpow_two_thirds_sq _ (hg _)] at hh
  have hu := mul_le_mul hmf hmg
    (finiteMean_nonneg (fun x => Real.rpow_nonneg (hg x) _)) hM
  have hs : finiteMean (fun x => (f x)^(2/3:ℝ)*(g x)^(2/3:ℝ))≤M := by
    nlinarith [hh.trans hu]
  have hc := finiteMean_mul_sq_le
    (fun x => (f x)^(2/3:ℝ)*(g x)^(2/3:ℝ))
    (fun x => (f x)^(1/3:ℝ)*(g x)^(1/3:ℝ))
  have he (x) : ((f x)^(2/3:ℝ)*(g x)^(2/3:ℝ))*
      ((f x)^(1/3:ℝ)*(g x)^(1/3:ℝ))=f x*g x := by
    calc
      _ = ((f x)^(2/3:ℝ)*(f x)^(1/3:ℝ))*((g x)^(2/3:ℝ)*(g x)^(1/3:ℝ)) := by ring
      _ = _ := by rw [rpow_thirds _ (hf _),rpow_thirds _ (hg _)]
  simp_rw [he,mul_pow,rpow_two_thirds_sq _ (hf _),rpow_two_thirds_sq _ (hg _),
    rpow_one_third_sq _ (hf _),rpow_one_third_sq _ (hg _)] at hc
  refine hc.trans ?_
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left hs (finiteMean_nonneg (fun x => mul_nonneg (Real.rpow_nonneg (hf x) _) (Real.rpow_nonneg (hg x) _)))

variable {X : Type*} [Fintype X] [Nonempty X]

omit [Nonempty X] in
lemma row_convolution_moment (R : X → X → ℝ) (hR : ∀ x y,0≤R x y)
    (M : ℝ) (hM : 0≤M)
    (hr : ∀ x,finiteMean (fun y => (R x y)^(4/3:ℝ))≤M)
    (hc : ∀ y,finiteMean (fun x => (R x y)^(4/3:ℝ))≤M) (x : X) :
    finiteMean (fun y => (finiteMean (fun z => R x z*R z y))^2) ≤ M^3 := by
  calc
    _ ≤ finiteMean (fun y => M*finiteMean (fun z => (R x z)^(4/3:ℝ)*(R z y)^(4/3:ℝ))) :=
      finiteMean_mono (fun y => young_cauchy (R x) (fun z => R z y)
        (hR x) (fun z => hR z y) M hM (hr x) (hc y))
    _ = M*finiteMean (fun z => finiteMean (fun y => (R x z)^(4/3:ℝ)*(R z y)^(4/3:ℝ))) := by
      rw [show ∀ f : X → ℝ,finiteMean (fun y => M*f y)=M*finiteMean f from
        fun f => by simpa only [mul_comm] using finiteMean_mul_const f M]
      rw [finiteMean_comm]
    _ ≤ M*(M*finiteMean (fun z => (R x z)^(4/3:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hM
      calc
        _ ≤ finiteMean (fun z => (R x z)^(4/3:ℝ)*M) := by
          apply finiteMean_mono
          intro z
          have he : finiteMean (fun y => (R x z)^(4/3:ℝ)*(R z y)^(4/3:ℝ))=
              (R x z)^(4/3:ℝ)*finiteMean (fun y => (R z y)^(4/3:ℝ)) := by
            simpa only [mul_comm] using finiteMean_mul_const (fun y => (R z y)^(4/3:ℝ))
              ((R x z)^(4/3:ℝ))
          rw [he]
          exact mul_le_mul_of_nonneg_left (hr z) (Real.rpow_nonneg (hR x z) _)
        _ = _ := by rw [finiteMean_mul_const,mul_comm]
    _ ≤ M*(M*M) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hr x) hM) hM
    _ = _ := by ring

lemma kernel_fourth_hs [DecidableEq X] (P : Matrix X X ℝ) (hP : ∀ x y,0≤P x y)
    (M : ℝ) (hM : 0≤M)
    (hr : ∀ x,finiteMean (fun y => ((Fintype.card X:ℝ)*P x y)^(4/3:ℝ))≤M)
    (hc : ∀ y,finiteMean (fun x => ((Fintype.card X:ℝ)*P x y)^(4/3:ℝ))≤M) :
    (∑ x,∑ y,((P^2) x y)^2)≤M^3 := by
  let N : ℝ := Fintype.card X
  have hN : 0<N := Nat.cast_pos.mpr Fintype.card_pos
  let R : X → X → ℝ := fun x y => N*P x y
  have he (x y : X) : finiteMean (fun z => R x z*R z y)=N*(P^2) x y := by
    simp only [finiteMean,R,pow_two,Matrix.mul_apply]
    have hh : ∑ z : X,(N*P x z)*(N*P z y)=N^2*(∑ z : X,P x z*P z y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [hh]
    change N^2*_ / N = N*_
    field_simp
  have hs (x) : (∑ y,((P^2) x y)^2)≤M^3/N := by
    have hh:=row_convolution_moment R (fun x y => mul_nonneg hN.le (hP x y)) M hM hr hc x
    simp_rw [he] at hh
    have he' : finiteMean (fun y => (N*(P^2) x y)^2)=N*(∑ y,((P^2) x y)^2) := by
      simp only [finiteMean,mul_pow,←Finset.mul_sum]
      change N^2*_ / N=N*_
      field_simp
    rw [he'] at hh
    apply (le_div_iff₀ hN).mpr
    simpa only [mul_comm] using hh
  calc
    _ ≤ ∑ _x : X,M^3/N := Finset.sum_le_sum (fun x _ => hs x)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      change N*(M^3/N)=M^3
      exact mul_div_cancel₀ _ (ne_of_gt hN)

end Thorp.AdaptiveBounds

namespace Thorp.AdaptiveBounds
open scoped BigOperators Classical
open Casimir UnitaryFinite
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma even_trace_hs (A : V →L[ℂ] V) (hs : IsSelfAdjoint A) (r : ℕ) :
    (LinearMap.trace ℂ V ((A^(2*r)).toLinearMap)).re =
      ∑ j, ‖(A^r) (stdOrthonormalBasis ℂ V j)‖^2 := by
  let B := stdOrthonormalBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ B.toBasis]
  simp only [Matrix.trace,Matrix.diag,Complex.re_sum,LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro j _
  have he : (A^(2*r)) (B j)=(A^r) ((A^r) (B j)) := by
    rw [two_mul,pow_add]
    rfl
  change (inner ℂ (B j) ((A^(2*r)) (B j))).re=‖(A^r) (B j)‖^2
  rw [he]
  conv_lhs => rw [←(hs.pow r).adjoint_eq,ContinuousLinearMap.adjoint_inner_right]
  rw [(hs.pow r).adjoint_eq,inner_self_eq_norm_sq_to_K]
  norm_cast

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

lemma coefficient_even_trace_amplification (a : G →* Equiv.Perm X) (x₀ : X)
    (ha : ∀ x, ∃ g, a g x₀=x) (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (P : Matrix X X ℝ) (A : V →L[ℂ] V)
    (hmap : ∀ w, IsFixed a x₀ ρ w → ∀ v,
      DensityTransfer.applyKernel (fun x y => P x y) (normalizedCoefficient a x₀ ha ρ w v) =
        normalizedCoefficient a x₀ ha ρ w (A v))
    (hs : IsSelfAdjoint A) (r : ℕ) :
    (Module.finrank ℂ (fixedSpace a x₀ ρ):ℝ) *
      (LinearMap.trace ℂ V ((A^(2*r)).toLinearMap)).re ≤
      ∑ x, ∑ y, ((P^r) x y)^2 := by
  let W := fixedSpace a x₀ ρ
  let B := stdOrthonormalBasis ℂ V
  let C := stdOrthonormalBasis ℂ W
  let w : Fin (Module.finrank ℂ W) → V := fun i => (C i : V)
  have hfix (i) : IsFixed a x₀ ρ (w i) := (C i).2
  have hw : Orthonormal ℂ w := C.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  let v : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ V) → EuclideanSpace ℂ X :=
    fun ij => normalizedCoefficient a x₀ ha ρ (w ij.1) (B ij.2)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [v]
    rw [normalizedCoefficient_inner a x₀ ha ρ hρ _ _ (hfix _) (hfix _)]
    rw [(orthonormal_iff_ite.mp hw), (orthonormal_iff_ite.mp B.orthonormal)]
    by_cases h1 : i.1=j.1 <;> by_cases h2 : i.2=j.2 <;>
      simp [h1,h2,Prod.ext_iff,eq_comm]
  have hp (s : ℕ) (i) (t : V) :
      DensityTransfer.applyKernel (fun x y => (P^s) x y) (normalizedCoefficient a x₀ ha ρ (w i) t) =
        normalizedCoefficient a x₀ ha ρ (w i) ((A^s) t) := by
    induction s with
    | zero => simp [applyKernel_one]
    | succ s ih =>
      rw [pow_succ',applyKernel_mul,ih,hmap _ (hfix _),pow_succ']
      rfl
  have hhs := DensityTransfer.hilbert_schmidt_family (fun x y => (P^r) x y) v hv
  have he : (∑ ij, ‖DensityTransfer.applyKernel (fun x y => (P^r) x y) (v ij)‖^2) =
      (Module.finrank ℂ W:ℝ) * ∑ j, ‖(A^r) (B j)‖^2 := by
    simp only [v,hp,normalizedCoefficient_norm a x₀ ha ρ hρ _ (hfix _)
      (hw.norm_eq_one _),Fintype.sum_prod_type]
    simp
  rw [he] at hhs
  rw [even_trace_hs A hs r]
  exact hhs

lemma palindrome_even_trace_amplification (d k : ℕ) (x₀ : Fin k ↪ Card d)
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) [Representation.IsIrreducible ρ]
    (hρ : IsUnitary ρ) (r : ℕ) :
    (Module.finrank ℂ (fixedSpace tupleAction x₀ ρ):ℝ) *
      (LinearMap.trace ℂ V (((sampleOperator ρ (palindromePerm d))^(2*r)).toLinearMap)).re ≤
    ∑ x, ∑ y, ((tupleKernel d k)^r) x y ^ 2 := by
  let ha := tupleAction_transitive x₀
  have hmap (w : V) (hw : IsFixed tupleAction x₀ ρ w) (v : V) :
      DensityTransfer.applyKernel (fun x y : Fin k ↪ Card d =>
        PairRouting.tupleProbability (palindromePerm d) x y)
        (normalizedCoefficient tupleAction x₀ ha ρ w v) =
      normalizedCoefficient tupleAction x₀ ha ρ w (sampleOperator ρ (palindromePerm d) v) := by
    have hh := coefficient_random tupleAction x₀ ha ρ hρ (palindromePerm d) w hw v
    have he : actionKernel tupleAction (palindromePerm d) =
        fun x y : Fin k ↪ Card d => PairRouting.tupleProbability (palindromePerm d) x y := by
      funext x y
      exact tupleAction_kernel _ x y
    rw [he,←sampleOperator_inv_apply,sampleOperator_inv _ hρ,
      (palindrome_selfadjoint d ρ hρ).adjoint_eq] at hh
    exact hh
  exact coefficient_even_trace_amplification tupleAction x₀ ha ρ hρ _ _ hmap
    (palindrome_selfadjoint d ρ hρ) r

end Thorp.AdaptiveBounds

namespace Thorp.AdaptiveBounds
open scoped BigOperators Classical
open Casimir UnitaryFinite

lemma tuple_fourth_hs (d k : ℕ) (x₀ : Fin k ↪ Card d) :
    (∑ x,∑ y,((tupleKernel d k)^2) x y ^ 2) ≤
      Real.exp ((3*densityConstant)*k) := by
  let : Nonempty (Fin k ↪ Card d) := ⟨x₀⟩
  have hr (x : Fin k ↪ Card d) :
      finiteMean (fun y => ((Fintype.card (Fin k ↪ Card d):ℝ)*tupleKernel d k x y)^(4/3:ℝ)) ≤
        Real.exp ((k:ℝ)*densityConstant) := by
    have hh:=row_moment d x
    norm_num only [palindromeRowMoment,Fintype.card_fin,show (1+(1/3:ℝ))=4/3 by norm_num] at hh
    exact hh
  have hc (y : Fin k ↪ Card d) :
      finiteMean (fun x => ((Fintype.card (Fin k ↪ Card d):ℝ)*tupleKernel d k x y)^(4/3:ℝ)) ≤
        Real.exp ((k:ℝ)*densityConstant) := by
    simp_rw [(tupleKernel_symm d k).apply y]
    exact hr y
  have hh:=kernel_fourth_hs (tupleKernel d k)
    (fun x y => PairRouting.tupleProbability_nonneg _ x y)
    (Real.exp ((k:ℝ)*densityConstant)) (Real.exp_nonneg _) hr hc
  apply hh.trans_eq
  rw [←Real.exp_nat_mul]
  congr 1
  norm_num
  ring

lemma fixed_trace_bound (d k : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (x₀ : Fin k ↪ Card d) :
    (Module.finrank ℂ (fixedSpace (V := Specht.hilbertSpace μ) tupleAction x₀
      (Specht.relabelledUnitary μ e)):ℝ) * traceMoment d μ e 4 ≤
        Real.exp ((3*densityConstant)*k) := by
  let ρ := Specht.relabelledUnitary μ e
  let := Specht.relabelledUnitary_irreducible μ e
  have hh := palindrome_even_trace_amplification (V:=Specht.hilbertSpace μ) d k x₀ ρ
    (Specht.relabelledUnitary_unitary μ e) 2
  change _ * traceMoment d μ e 4 ≤ _ at hh
  exact hh.trans (tuple_fourth_hs d k x₀)

lemma dimension_trace_bound (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) :
    (Module.finrank ℂ (Specht.space μ):ℝ)*traceMoment d μ e 4 ≤
      Real.exp ((1+3*densityConstant)*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  let k := μ.card-μ.rowLen 0
  have hn : μ.card=2^d := by
    rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hk : k≤2^d := by dsimp [k]; omega
  let x₀ : Fin k ↪ Card d := (Fin.castLEEmb (show k≤Fintype.card (Card d) by simpa [card_positions] using hk)).trans
    (Fintype.equivFin (Card d)).symm.toEmbedding
  let m := Module.finrank ℂ (fixedSpace (V := Specht.hilbertSpace μ) tupleAction x₀
    (Specht.relabelledUnitary μ e))
  have hd : (Module.finrank ℂ (Specht.space μ):ℝ) ≤ (m:ℝ)*((2^d).choose k:ℝ) := by
    have hh := Specht.relabelled_tuple_dimension μ e x₀
    simp only [Fintype.card_fin] at hh
    change Module.finrank ℂ (Specht.hilbertSpace μ) * k.choose k ≤ m * μ.card.choose k at hh
    rw [Nat.choose_self,mul_one,Specht.finrank_hilbertSpace,hn] at hh
    exact_mod_cast hh
  have hm := fixed_trace_bound d k μ e x₀
  by_cases ht : 0≤traceMoment d μ e 4
  · calc
      _ ≤ ((m:ℝ)*((2^d).choose k:ℝ))*traceMoment d μ e 4 :=
        mul_le_mul_of_nonneg_right hd ht
      _ = ((2^d).choose k:ℝ)*((m:ℝ)*traceMoment d μ e 4) := by ring
      _ ≤ ((2^d).choose k:ℝ)*Real.exp ((3*densityConstant)*k) :=
        mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
      _ ≤ Real.exp (levelScale (2^d) k)*Real.exp ((3*densityConstant)*levelScale (2^d) k) := by
        apply mul_le_mul (choose_le_exp_levelScale _ _ (by positivity) hk) _ (by positivity) (Real.exp_nonneg _)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (levelScale_ge _ _ hk) (by linarith [densityConstant_pos])
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (le_of_not_ge ht)).trans (Real.exp_nonneg _)

end Thorp.AdaptiveBounds

namespace Thorp.AdaptiveBounds
open scoped BigOperators Classical

section
open Casimir UnitaryFinite

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

lemma positiveSquare_norm (T : V →L[ℂ] V) : ‖positiveSquare T‖=‖T‖^2 := by
  change ‖T*star T‖=‖T‖^2
  simpa only [pow_two] using CStarRing.norm_self_mul_star (x:=T)

lemma positiveSquare_selfadjoint (T : V →L[ℂ] V) : IsSelfAdjoint (positiveSquare T) := by
  change IsSelfAdjoint (T*star T)
  simp only [isSelfAdjoint_iff,star_mul,star_star]

omit [FiniteDimensional ℂ V] in
lemma trace_mul_fourth_comm (A B : V →L[ℂ] V) :
    LinearMap.trace ℂ V ((A*B)^4).toLinearMap =
      LinearMap.trace ℂ V ((B*A)^4).toLinearMap := by
  change LinearMap.trace ℂ V ((A.toLinearMap*B.toLinearMap)^4) =
    LinearMap.trace ℂ V ((B.toLinearMap*A.toLinearMap)^4)
  rw [show (A.toLinearMap*B.toLinearMap)^4=
    (A.toLinearMap*(B.toLinearMap*A.toLinearMap)^3)*B.toLinearMap by noncomm_ring]
  rw [LinearMap.trace_mul_comm]
  congr 1

lemma F_norm (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    ‖F d μ e rev‖=‖K d μ e‖ := by
  change ‖positiveSquare (V:=Specht.hilbertSpace μ) (SparseContact.sweepOperator d μ e rev)‖=_
  rw [positiveSquare_norm]
  exact StrongTail.sweep_sq_palindrome d μ e rev

lemma F_false (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) : F d μ e false=K d μ e := by
  simp only [F,positiveSquare,SparseContact.sweepOperator]
  exact (sampleOperator_palindrome _ _ (Specht.relabelledUnitary_unitary μ e)).symm

lemma trace_eq (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    fourthTrace d μ e rev=traceMoment d μ e 4 := by
  cases rev with
  | false => rw [fourthTrace,F_false]; rfl
  | true =>
    unfold fourthTrace traceMoment
    rw [←F_false]
    simp only [F,positiveSquare,SparseContact.sweepOperator,ite_true]
    rw [sampleOperator_inv _ (Specht.relabelledUnitary_unitary μ e),ContinuousLinearMap.adjoint_adjoint]
    congr 1
    exact trace_mul_fourth_comm (V:=Specht.hilbertSpace μ) _ _

lemma fourthTrace_real (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    (fourthTrace d μ e rev:ℂ)=
      LinearMap.trace ℂ (Specht.hilbertSpace μ) ((F d μ e rev)^4).toLinearMap := by
  exact trace_power_real (V:=Specht.hilbertSpace μ) _
    (positiveSquare_selfadjoint (V:=Specht.hilbertSpace μ) _) 4

lemma fourthTrace_bound (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ) (rev : Bool) :
    fourthTrace d μ e rev≤Real.exp (-Real.log (Module.finrank ℂ (Specht.space μ):ℝ)+
      (1+3*densityConstant)*levelScale (2^d) (μ.card-μ.rowLen 0)) := by
  rw [trace_eq]
  let D : ℝ := Module.finrank ℂ (Specht.space μ)
  have hD : 0<D := by
    dsimp [D]
    exact_mod_cast Specht.dimension_pos μ
  have hh:=dimension_trace_bound d μ e
  have he : Real.exp (-Real.log D+(1+3*densityConstant)*levelScale (2^d) (μ.card-μ.rowLen 0))=
      Real.exp ((1+3*densityConstant)*levelScale (2^d) (μ.card-μ.rowLen 0))/D := by
    rw [Real.exp_add,Real.exp_neg,Real.exp_log hD]
    ring
  change _≤Real.exp (-Real.log D+_)
  rw [he]
  apply (le_div_iff₀ hD).mpr
  simpa only [mul_comm] using hh

lemma zero_level_dimension (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Specht.Cell μ)
    (hk : μ.card-μ.rowLen 0=0) : Module.finrank ℂ (Specht.space μ)=1 := by
  have hr : μ.rowLen 0=μ.card := by have hh:=Specht.rowLen_zero_le_card μ; omega
  have hnp : 0<μ.card := by
    rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
    positivity
  have hcol : 0<μ.colLen 0 := by
    have hh : (0,0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    exact YoungDiagram.mem_iff_lt_colLen.mp hh
  have hg : μ.card.factorial ≤ Fintype.card (Specht.rowGroup μ) := by
    rw [Specht.card_rowGroup,←hr]
    simpa using (Finset.single_le_prod (f := fun i : Fin (μ.colLen 0) => (μ.rowLen i).factorial)
      (s := Finset.univ) (fun i _ => Nat.factorial_pos (μ.rowLen i))
      (Finset.mem_univ (⟨0,hcol⟩ : Fin (μ.colLen 0))))
  have hc := Specht.card_tabloid_mul_row μ
  have hD : Module.finrank ℂ (Specht.space μ) ≤ Fintype.card (Specht.Tabloid μ) := by
    simpa using Submodule.finrank_le (Specht.space μ)
  have hp := Specht.dimension_pos μ
  have hf := Nat.factorial_pos μ.card
  nlinarith

end
open Casimir

theorem adaptive_main : MainStatement := by
  obtain ⟨a,ha,hlevel⟩ := level_contraction
  obtain ⟨b,hb,hdim⟩ := Harmonic.dimension_contraction
  refine ⟨a,1,1+3*densityConstant,min a b/4,ha,by norm_num,
    by linarith [densityConstant_pos],by positivity,?_⟩
  intro d μ e rev
  dsimp only
  let L := levelScale (2^d) (μ.card-μ.rowLen 0)
  let D : ℝ := Module.finrank ℂ (Specht.space μ)
  have hμ : μ.card=2^d := by rw [←Specht.card_cell,←Fintype.card_congr e,card_positions]
  have hL : 0≤L := (Nat.cast_nonneg (μ.card-μ.rowLen 0)).trans
    (levelScale_ge (2^d) _ (by omega))
  have hD : 0≤Real.log D := Real.log_nonneg (by
    dsimp [D]
    exact_mod_cast Specht.dimension_pos μ)
  refine ⟨?_,?_,?_⟩
  · rw [F_norm]
    by_cases hk : 0<μ.card-μ.rowLen 0
    · exact hlevel d μ e hk
    · have hz : μ.card-μ.rowLen 0=0 := by omega
      simpa only [hz,levelScale,Nat.cast_zero,zero_mul,mul_zero,Real.exp_zero] using
        K_norm_le_one d μ e
  · simpa only [neg_mul,one_mul] using fourthTrace_bound d μ e rev
  · by_cases hk : 0<μ.card-μ.rowLen 0
    · have hw := hlevel d μ e hk
      have hd := hdim d μ e hk
      change ‖K d μ e‖≤Real.exp (-a*L) at hw
      change ‖K d μ e‖≤Real.exp (-b*Real.log D) at hd
      have hg:=Harmonic.exp_intersection (norm_nonneg (K d μ e)) hw hd
      have hcoef : (-a*L+-b*Real.log D)/2 ≤ -2*(min a b/4)*(Real.log D+L) := by
        have h₁:=mul_le_mul_of_nonneg_right (min_le_left a b) hL
        have h₂:=mul_le_mul_of_nonneg_right (min_le_right a b) hD
        nlinarith
      have hg' :=hg.trans (Real.exp_le_exp.mpr hcoef)
      have hs :=StrongTail.sweep_sq_palindrome d μ e rev
      change ‖SparseContact.sweepOperator d μ e rev‖^2=‖K d μ e‖ at hs
      rw [←hs] at hg'
      have he : Real.exp (-(min a b/4)*(Real.log D+L))^2=
          Real.exp (-2*(min a b/4)*(Real.log D+L)) := by
        rw [pow_two,←Real.exp_add]
        congr 1; ring
      change ‖SparseContact.sweepOperator d μ e rev‖≤Real.exp (-(min a b/4)*(Real.log D+L))
      nlinarith [Real.exp_pos (-(min a b/4)*(Real.log D+L))]
    · have hz : μ.card-μ.rowLen 0=0 := by omega
      rw [zero_level_dimension d μ e hz]
      simpa only [hz,levelScale,Nat.cast_zero,Nat.cast_one,Real.log_one,zero_mul,
        add_zero,mul_zero,Real.exp_zero] using SparseContact.sweep_norm_le_one d μ e rev

end Thorp.AdaptiveBounds

end ThorpNine.Adaptive

end OAI
