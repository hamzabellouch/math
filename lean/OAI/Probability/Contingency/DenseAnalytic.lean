import Mathlib
import OAI.Probability.Contingency.PieceQuantiles

namespace OAI

/-! Dense Analytic. -/

noncomputable section

open Set MeasureTheory
open scoped Pointwise
open Set MeasureTheory
open scoped Pointwise
namespace Contingency.Dense
noncomputable section
variable {a c q : ℕ}

theorem normalized_continuous (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (i : Fin (a+1)) (j : Fin (c+1)) :
    Continuous (fun u => normalized R P w u i j) := by
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp only [normalized,scaled,complete_corner,complete_bottom,complete_right,complete_free]
  all_goals fun_prop

theorem penalty_continuous (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) : Continuous (penalty R P w B d) := by
  apply continuous_const.max
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun s _ =>
    (normalized_continuous R P w s.1 s.2).neg.sub continuous_const

theorem density_continuous (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d A : ℝ) : Continuous (density R P w B d A) := by
  unfold density
  exact continuous_const.rpow (continuous_const.mul (penalty_continuous _ _ _ _ _)) (fun _ => Or.inl (by norm_num))

theorem density_le_one (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d A : ℝ) (hA : 0 ≤ A) (u) : density R P w B d A u ≤ 1 := by
  unfold density
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) (penalty_nonneg _ _ _ _ _ _))

def densityWeight (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d A : ℝ) (hA : 0 ≤ A) : Interpolation.GoodWeight q where
  f u := density R P w B d A (fun s => u (e.symm s))
  continuous := (density_continuous _ _ _ _ _ _).comp (continuous_pi fun s => continuous_apply _)
  positive u := density_pos _ _ _ _ _ _ _
  bound := 1
  bounded u := by rw [Real.norm_eq_abs,abs_of_pos (density_pos _ _ _ _ _ _ _)]; exact density_le_one _ _ _ _ _ _ hA _

theorem densityWeight_logconcave (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d A : ℝ) (hA : 0 ≤ A)
    (u v : Fin q → ℝ) (α β : ℝ) (ha : 0 ≤ α) (hb : 0 ≤ β) (hab : α+β=1) :
    (densityWeight e R P w B d A hA).f u^α*(densityWeight e R P w B d A hA).f v^β ≤
      (densityWeight e R P w B d A hA).f (α • u+β • v) :=
  density_logconcave R P w B d A hA (fun s => u (e.symm s)) (fun s => v (e.symm s)) α β ha hb hab

end
end Contingency.Dense

namespace Contingency.Interpolation
noncomputable section
variable {q : ℕ}

theorem mix_contains (S T : Finset (OpenBox q)) (hsub : boxUnion S ⊆ boxUnion T)
    (t : ℝ) (ht : 0<t) (ht1 : t<1) : boxUnion S ⊆ boxUnion (mixBoxes S T (1-t) t) := by
  intro x hx
  apply (mem_mixBoxes S T (1-t) t (by linarith) ht x).mpr
  refine ⟨x,hx,x,hsub hx,?_⟩
  ext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

 
theorem mass_gain (S T : Finset (OpenBox q)) (F : GoodWeight q)
    (hsub : boxUnion S ⊆ boxUnion T) (hS : (boxUnion S).Nonempty)
    (hsmall : 2*(∫ x in boxUnion S,F.f x) ≤ ∫ x in boxUnion T,F.f x)
    (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (hc : ∀ x y,F.f x^(1-t)*F.f y^t ≤ F.f ((1-t) • x+t • y)) :
    t*Real.log 2*(∫ x in boxUnion S,F.f x) ≤
      ∫ x in boxUnion (mixBoxes S T (1-t) t) \ boxUnion S,F.f x := by
  let m := ∫ x in boxUnion S,F.f x
  have hm : 0 < m := F.integral_pos S hS
  have hinter := logconcave_interpolation S T F (1-t) t (by linarith) ht (by ring) hc
  have hlower : (2:ℝ)^t*m ≤ ∫ x in boxUnion (mixBoxes S T (1-t) t),F.f x := by
    calc
      _ = m^(1-t)*(2*m)^t := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hm.le]
        rw [mul_left_comm,← Real.rpow_add hm]
        simp
      _ ≤ m^(1-t)*(∫ x in boxUnion T,F.f x)^t :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hsmall ht.le) (Real.rpow_nonneg hm.le _)
      _ ≤ _ := hinter
  have hexp : 1+t*Real.log 2 ≤ (2:ℝ)^t := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [Real.add_one_le_exp (Real.log 2*t)]
  rw [setIntegral_sdiff (boxUnion_measurable S) (F.integrable _) (mix_contains S T hsub t ht ht1)]
  have hh := mul_le_mul_of_nonneg_right hexp hm.le
  dsimp [m] at hh hlower
  nlinarith only [hh,hlower]

end
end Contingency.Interpolation

 

 

open Set MeasureTheory
open scoped Pointwise BigOperators
namespace Contingency.Dense
noncomputable section
variable {q : ℕ} {I : Type*} [Fintype I]

 

def region (f : I → (Fin q → ℝ) → ℝ) (τ : ℝ) : Set (Fin q → ℝ) :=
  {x | ∀ i,τ ≤ f i x}

theorem region_measurable (f : I → (Fin q → ℝ) → ℝ) (hf : ∀ i,Continuous (f i)) (τ : ℝ) :
    MeasurableSet (region f τ) := by
  have he : region f τ=⋂ i,{x | τ ≤ f i x} := by ext x; simp [region]
  rw [he]
  exact MeasurableSet.iInter fun i => isClosed_le continuous_const (hf i) |>.measurableSet

omit [Fintype I] in
theorem homothety_affine (f : I → (Fin q → ℝ) → ℝ)
    (hf : ∀ i x y (α β : ℝ),α+β=1 → f i (α • x+β • y)=α*f i x+β*f i y)
    (i : I) (u x : Fin q → ℝ) (r : ℝ) :
    f i (AffineMap.homothety u r x)=r*f i x+(1-r)*f i u := by
  have he : AffineMap.homothety u r x=r • x+(1-r) • u := by
    ext j
    simp only [AffineMap.homothety_apply, vadd_eq_add,vsub_eq_sub,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,hf i x u r (1-r) (by ring)]

omit [Fintype I] in
theorem inner_image_subset (f : I → (Fin q → ℝ) → ℝ)
    (hf : ∀ i x y (α β : ℝ),α+β=1 → f i (α • x+β • y)=α*f i x+β*f i y)
    (u : Fin q → ℝ) (s α : ℝ) (hu : ∀ i,s ≤ f i u)
    (ha : 0 ≤ α) (ha1 : α ≤ 1) :
    AffineMap.homothety u (1-α) '' region f 0 ⊆ region f (α*s) := by
  rintro z ⟨x,hx,rfl⟩ i
  rw [homothety_affine f hf,sub_sub_cancel]
  exact add_le_add (mul_nonneg (by linarith) (hx i)) (mul_le_mul_of_nonneg_left (hu i) ha) |>.trans' (by ring_nf; rfl)

omit [Fintype I] in
theorem relaxed_subset_image (f : I → (Fin q → ℝ) → ℝ)
    (hf : ∀ i x y (α β : ℝ),α+β=1 → f i (α • x+β • y)=α*f i x+β*f i y)
    (u : Fin q → ℝ) (s γ : ℝ) (hs : 0<s) (hu : ∀ i,s ≤ f i u) (hg : 0 ≤ γ) :
    region f (-γ) ⊆ AffineMap.homothety u (1+γ/s) '' region f 0 := by
  intro x hx
  let r := 1+γ/s
  have hr : 0<r := by dsimp [r]; positivity
  let z := AffineMap.homothety u (1/r) x
  refine ⟨z,?_,?_⟩
  · intro i
    dsimp [z]
    rw [homothety_affine f hf]
    have hr1 : 1 ≤ r := by
      dsimp [r]
      have hh : 0 ≤ γ/s := by positivity
      linarith
    have hcoef : 0 ≤ 1-1/r := by have := (div_le_one hr).mpr hr1; linarith
    have h1 := mul_le_mul_of_nonneg_left (hx i) (show 0 ≤ 1/r by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hu i) hcoef
    have he : (1/r)*(-γ)+(1-1/r)*s=0 := by dsimp [r]; field_simp; ring
    linarith only [h1,h2,he]
  · ext j
    simp only [z,AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    change r*((1/r*(x j-u j)+u j)-u j)+u j=x j
    field_simp
    ring

theorem homothety_volume (u : Fin q → ℝ) (r : ℝ) (hr : 0 ≤ r) (S : Set (Fin q → ℝ)) :
    volume (AffineMap.homothety u r '' S)=ENNReal.ofReal (r^q)*volume S := by
  rw [Measure.addHaar_image_homothety]
  simp [abs_of_nonneg (pow_nonneg hr _)]

omit [Fintype I] in
theorem inner_volume (f : I → (Fin q → ℝ) → ℝ)
    (hf : ∀ i x y (α β : ℝ),α+β=1 → f i (α • x+β • y)=α*f i x+β*f i y)
    (u : Fin q → ℝ) (s α : ℝ) (hu : ∀ i,s ≤ f i u)
    (ha : 0 ≤ α) (ha1 : α ≤ 1) :
    ENNReal.ofReal ((1-α)^q)*volume (region f 0) ≤ volume (region f (α*s)) := by
  rw [← homothety_volume u (1-α) (by linarith)]
  exact measure_mono (inner_image_subset f hf u s α hu ha ha1)

omit [Fintype I] in
theorem relaxed_volume (f : I → (Fin q → ℝ) → ℝ)
    (hf : ∀ i x y (α β : ℝ),α+β=1 → f i (α • x+β • y)=α*f i x+β*f i y)
    (u : Fin q → ℝ) (s γ : ℝ) (hs : 0<s) (hu : ∀ i,s ≤ f i u) (hg : 0 ≤ γ) :
    volume (region f (-γ)) ≤ ENNReal.ofReal (Real.exp ((q:ℝ)*γ/s))*volume (region f 0) := by
  have hh := measure_mono (μ:=volume) (relaxed_subset_image f hf u s γ hs hu hg)
  rw [homothety_volume u (1+γ/s) (by positivity)] at hh
  apply hh.trans
  gcongr
  calc
    (1+γ/s)^q ≤ (Real.exp (γ/s))^q := pow_le_pow_left₀ (by positivity) (by linarith only [Real.add_one_le_exp (γ/s)]) q
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end
end Contingency.Dense

 

 

open Set MeasureTheory
open scoped Pointwise BigOperators
namespace Contingency.Dense
noncomputable section
variable {a c q : ℕ}

def constraints (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (s : Fin (a+1)×Fin (c+1)) (x : Fin q → ℝ) : ℝ :=
  normalized R P w (fun s => x (e.symm s)) s.1 s.2

theorem constraints_affine (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (i) (x y : Fin q → ℝ) (α β : ℝ) (hab : α+β=1) :
    constraints e R P w i (α • x+β • y)=α*constraints e R P w i x+β*constraints e R P w i y :=
  normalized_affine R P w _ _ α β hab _ _

theorem constraints_continuous (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (i) : Continuous (constraints e R P w i) :=
  (normalized_continuous R P w _ _).comp (continuous_pi fun coordinate => continuous_apply (e.symm coordinate))

theorem constraints_lipschitz (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B d : ℝ) (hB : 0<B) (hd : 0 ≤ d) (hdim : (a*c:ℕ) ≤ d)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/B)
    (x y : Fin q → ℝ) (i) :
    |constraints e R P w i x-constraints e R P w i y| ≤ d/B*‖x-y‖ := by
  apply (normalized_lipschitz R P w B d hB hdim hR hP hRmax hPmax hw0 hw _ _ _ _).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hd hB.le)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro s
  exact norm_le_pi_norm (x-y) (e.symm s)

theorem region_bounded (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B : ℝ) (hB : 0<B)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j) (heq : (∑ i,R i)=∑ j,P j)
    (hw : ∀ i j,scale R P i.castSucc j.castSucc/(2*B) ≤ w i j) :
    region (constraints e R P w) 0 ⊆ Set.pi Set.univ (fun _ => Set.Icc 0 (2*B)) := by
  intro x hx
  have hh := polytope_bounded R P w B hB hR hP heq hw (fun s => x (e.symm s)) (fun i j => hx (i,j))
  intro i _
  simpa only [e.symm_apply_apply,Set.mem_Icc] using hh (e i)

theorem region_volume_finite (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B : ℝ) (hB : 0<B)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j) (heq : (∑ i,R i)=∑ j,P j)
    (hw : ∀ i j,scale R P i.castSucc j.castSucc/(2*B) ≤ w i j) :
    volume (region (constraints e R P w) 0)<⊤ := by
  apply (measure_mono (region_bounded e R P w B hB hR hP heq hw)).trans_lt
  exact (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top

theorem region_interior (e : Fin q ≃ Fin a×Fin c) (d : ℝ) (hd : 0<d)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j) (heq : (∑ i,R i)=∑ j,P j)
    (ha : (a+1:ℕ) ≤ d) (hc : (c+1:ℕ) ≤ d) (hw : ∀ i j,0<w i j) :
    ∃ u : Fin q → ℝ,∀ i,1/(2*d) ≤ constraints e R P w i u := by
  obtain ⟨u,hu⟩ := interior_point d hd R P w hR hP heq ha hc hw
  refine ⟨fun i => u (e i),fun i => ?_⟩
  simpa only [constraints,e.apply_symm_apply] using hu i.1 i.2

theorem inner_half_volume (f : (Fin (a+1)×Fin (c+1)) → (Fin q → ℝ) → ℝ)
    (hf : ∀ i x y (α β : ℝ),α+β=1 → f i (α • x+β • y)=α*f i x+β*f i y)
    (d : ℝ) (hd : 2 ≤ d) (hq : (q:ℝ) ≤ d) (u : Fin q → ℝ)
    (hu : ∀ i,1/(2*d) ≤ f i u) :
    (1/2:ENNReal)*volume (region f 0) ≤ volume (region f (2*d/d^8)) := by
  have hd0 : 0<d := by linarith
  let α := 4*d^2/d^8
  have ha : 0 ≤ α := by dsimp [α]; positivity
  have had : α*d ≤ 1/2 := by
    have he : α*d=4/d^5 := by dsimp [α]; field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    have hp : (2:ℝ)^5 ≤ d^5 := pow_le_pow_left₀ (by norm_num) hd 5
    norm_num at hp
    linarith
  have ha1 : α ≤ 1 := by nlinarith
  have hpow : 1/2 ≤ (1-α)^q := by
    have hh := one_add_mul_le_pow (a := -α) (by linarith) q
    have hq' := mul_le_mul_of_nonneg_right hq ha
    have he : 1+-α=1-α := by ring
    rw [he] at hh
    nlinarith only [hh,hq',had]
  have hh := inner_volume f hf u (1/(2*d)) α hu ha ha1
  have he : α*(1/(2*d))=2*d/d^8 := by dsimp [α]; field_simp; ring
  rw [he] at hh
  have hlo : (1/2:ENNReal) ≤ ENNReal.ofReal ((1-α)^q) := by
    have ht := ENNReal.ofReal_le_ofReal hpow
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using ht
  calc
    _ ≤ ENNReal.ofReal ((1-α)^q)*volume (region f 0) := by gcongr
    _ ≤ _ := hh

theorem relaxed_volume_dense (f : (Fin (a+1)×Fin (c+1)) → (Fin q → ℝ) → ℝ)
    (hf : ∀ i x y (α β : ℝ),α+β=1 → f i (α • x+β • y)=α*f i x+β*f i y)
    (d : ℝ) (hd : 0<d) (hq : (q:ℝ) ≤ d) (u : Fin q → ℝ)
    (hu : ∀ i,1/(2*d) ≤ f i u) (γ : ℝ) (hg : 0 ≤ γ) :
    volume (region f (-γ)) ≤ ENNReal.ofReal (Real.exp (2*d^2*γ))*volume (region f 0) := by
  apply (relaxed_volume f hf u (1/(2*d)) γ (by positivity) hu hg).trans
  gcongr
  have he : (q:ℝ)*γ/(1/(2*d))=(q:ℝ)*(2*d*γ) := by field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hq (show 0 ≤ 2*d*γ by positivity)
  nlinarith only [hh]

end
end Contingency.Dense

 

 

open Set MeasureTheory
open scoped BigOperators
namespace Contingency.Dense
noncomputable section
variable {q : ℕ}

theorem half_times_four_thirds : (1/2:ENNReal)*(4/3)=2/3 := by
  have h : (1/2:NNReal)*(4/3)=2/3 := by norm_num
  have hh := congrArg (fun x : NNReal => (x : ENNReal)) h
  simpa only [ENNReal.coe_mul,ENNReal.coe_div (by norm_num : (2:NNReal)≠0),ENNReal.coe_div (by norm_num : (3:NNReal)≠0),ENNReal.coe_one,ENNReal.coe_ofNat] using hh
theorem geometric_constant : (1-(2/3:ENNReal))⁻¹*(4/3)=4 := by
  have hs : (1-(2/3:NNReal))=1/3 := by
    apply NNReal.eq
    rw [NNReal.coe_sub (by norm_num [div_le_one (by norm_num : (0:NNReal)<3)] : (2/3:NNReal) ≤ 1)]
    norm_num
  have h : (1-(2/3:NNReal))⁻¹*(4/3)=4 := by rw [hs]; norm_num
  have hh := congrArg (fun x : NNReal => (x : ENNReal)) h
  simpa only [ENNReal.coe_mul,ENNReal.coe_inv (show (1-(2/3:NNReal))≠0 by rw [hs]; norm_num),ENNReal.coe_sub,ENNReal.coe_div (by norm_num : (3:NNReal)≠0),ENNReal.coe_one,ENNReal.coe_ofNat] using hh

theorem decay_nat (j : ℕ) : ENNReal.ofReal ((2:ℝ)^(-(j:ℝ)))=(1/2:ENNReal)^j := by
  rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,← inv_pow,ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
  norm_num

 

theorem density_layer_bound (p : (Fin q → ℝ) → ℝ) (hp : Measurable p)
    (hp0 : ∀ x,0 ≤ p x) (A : ℝ) (hA : 0<A) (S : Set (Fin q → ℝ))
    (V : ENNReal) (hvol : ∀ j : ℕ,
      volume ({x | p x < ((j:ℝ)+1)/A} ∩ S) ≤ (4/3:ENNReal)^(j+1)*V) :
    (∫⁻ x in S,ENNReal.ofReal ((2:ℝ)^(-A*p x))) ≤ 4*V := by
  let T (j : ℕ) := {x | p x < ((j:ℝ)+1)/A}
  have hm (j : ℕ) : MeasurableSet (T j) := measurableSet_lt hp measurable_const
  let f (j : ℕ) := (T j).indicator (fun _ => (1/2:ENNReal)^j)
  have hf (j : ℕ) : Measurable (f j) := measurable_const.indicator (hm j)
  have hpoint (x : Fin q → ℝ) : ENNReal.ofReal ((2:ℝ)^(-A*p x)) ≤ ∑' j,f j x := by
    let j := ⌊A*p x⌋₊
    have hj : x∈T j := by
      apply (lt_div_iff₀ hA).mpr
      simpa only [mul_comm] using Nat.lt_floor_add_one (A*p x)
    apply le_trans _ (ENNReal.le_tsum j)
    rw [show f j x=(1/2:ENNReal)^j from Set.indicator_of_mem hj _]
    rw [← decay_nat]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := Nat.floor_le (mul_nonneg hA.le (hp0 x))
    dsimp [j]
    linarith only [hh]
  calc
    _ ≤ ∫⁻ x in S,∑' j,f j x := lintegral_mono hpoint
    _ = ∑' j, (1/2:ENNReal)^j*volume (T j∩S) := by
      rw [lintegral_tsum fun j => (hf j).aemeasurable]
      congr 1
      funext j
      rw [lintegral_indicator (hm j),lintegral_const,Measure.restrict_apply MeasurableSet.univ]
      rw [Set.univ_inter,Measure.restrict_apply (hm j)]
    _ ≤ ∑' j,(1/2:ENNReal)^j*((4/3:ENNReal)^(j+1)*V) :=
      ENNReal.tsum_le_tsum fun j => by gcongr; exact hvol j
    _ = 4*V := by
      have hterm (j : ℕ) : (1/2:ENNReal)^j*((4/3:ENNReal)^(j+1)*V)=
          (2/3:ENNReal)^j*((4/3)*V) := by
        rw [pow_succ]
        calc
          _ = ((1/2:ENNReal)*(4/3))^j*((4/3)*V) := by rw [mul_pow]; ring
          _ = _ := by rw [half_times_four_thirds]
      simp_rw [hterm]
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
      rw [← mul_assoc,geometric_constant]

theorem exp_quarter_bound (x : ℝ) (hx : x ≤ 1/4) : Real.exp x ≤ 4/3 := by
  apply (Real.exp_le_exp.mpr hx).trans
  have hh := Real.exp_bound_div_one_sub_of_interval (x := 1/4) (by norm_num) (by norm_num)
  norm_num at hh ⊢
  exact hh

theorem dense_exponent_layer (d : ℝ) (hd : 4 ≤ d) (j : ℕ) :
    Real.exp (2*d^2*(d/d^8+((j:ℝ)+1)/d^4)) ≤ (4/3:ℝ)^(j+1) := by
  have hd0 : 0<d := by linarith
  let α := 2/d^2
  let β := 2/d^5
  have hα : α ≤ 1/8 := by
    dsimp [α]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (d-4)]
  have hβ : β ≤ 1/8 := by
    dsimp [β]
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hd 5
    norm_num at hh
    linarith
  have he : 2*d^2*(d/d^8+((j:ℝ)+1)/d^4)=β+((j:ℝ)+1)*α := by
    dsimp [α,β]
    field_simp
  have hβ0 : 0 ≤ β := by dsimp [β]; positivity
  calc
    _ = Real.exp (β+((j:ℝ)+1)*α) := by rw [he]
    _ ≤ Real.exp (((j:ℝ)+1)*(α+β)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg (show 0 ≤ (j:ℝ) by positivity) hβ0]
    _ = Real.exp (α+β)^(j+1) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (exp_quarter_bound _ (by linarith)) _

end
end Contingency.Dense

 

 

open Set
namespace Contingency.Grid
noncomputable section
variable {q : ℕ}

def inside (v : Fin q → ℕ) (x : Fin q → ℝ) : Prop :=
  ∀ i,(v i:ℝ)<x i ∧ x i<(v i:ℝ)+1

def path (v w : Fin q → ℕ) (n : ℕ) : Fin q → ℕ :=
  fun i => if i.val<n then w i else v i

@[simp] theorem path_zero (v w : Fin q → ℕ) : path v w 0=v := by ext i; simp [path]
@[simp] theorem path_end (v w : Fin q → ℕ) : path v w q=w := by ext i; simp [path,i.isLt]

theorem exists_label_step {α : Type*} (f : ℕ → α) (n : ℕ) (h : f 0 ≠ f n) :
    ∃ k,k<n ∧ f k ≠ f (k+1) := by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    by_cases hh : f 0=f n
    · exact ⟨n,Nat.lt_succ_self n,fun he => h (hh.trans he)⟩
    · obtain ⟨k,hk,he⟩ := ih hh
      exact ⟨k,hk.trans (Nat.lt_succ_self n),he⟩

theorem path_step (v w : Fin q → ℕ) (k : Fin q) :
    path v w (k.val+1)=Function.update (path v w k.val) k (w k) := by
  ext i
  by_cases hi : i=k
  · subst i; simp [path]
  · have hh : i.val ≠ k.val := fun h => hi (Fin.ext h)
    simp only [path,Function.update_of_ne hi]
    split_ifs <;> omega

def neighbors (v w : Fin q → ℕ) (i : Fin q) : Prop :=
  (v i+1=w i ∨ w i+1=v i) ∧ ∀ j,j ≠ i → v j=w j

 
def face (v w : Fin q → ℕ) (i : Fin q) : Set (Fin q → ℝ) :=
  {z | z i=(max (v i) (w i):ℕ) ∧ ∀ j,j ≠ i → (v j:ℝ) ≤ z j ∧ z j ≤ (v j:ℝ)+1}

theorem adjacent_of_close (v w : ℕ) (x z r : ℝ)
    (hx : (v:ℝ)<x ∧ x<(v:ℝ)+1) (hz : (w:ℝ)<z ∧ z<(w:ℝ)+1)
    (hclose : |x-z|<r) (hr : r ≤ 1) (hne : v ≠ w) :
    v+1=w ∨ w+1=v := by
  have hc := abs_lt.mp hclose
  have hvw : (v:ℝ)<(w:ℝ)+2 := by linarith
  have hwv : (w:ℝ)<(v:ℝ)+2 := by linarith
  have hvw' : v<w+2 := by exact_mod_cast hvw
  have hwv' : w<v+2 := by exact_mod_cast hwv
  omega

 

theorem cut_face_close (v w : Fin q → ℕ) (label : (Fin q → ℕ) → Bool)
    (hl : label v ≠ label w) (x z : Fin q → ℝ) (hx : inside v x) (hz : inside w z)
    (r : ℝ) (hr : r ≤ 1) (hc : ∀ i,|x i-z i|<r) :
    ∃ u u' : Fin q → ℕ,∃ i : Fin q,
      neighbors u u' i ∧ label u ≠ label u' ∧
      (∀ j,u j=v j ∨ u j=w j) ∧ (∀ j,u' j=v j ∨ u' j=w j) ∧
      ∃ p∈face u u' i,∀ j,|p j-z j|<r := by
  have hp : label (path v w 0) ≠ label (path v w q) := by simpa using hl
  obtain ⟨k,hk,hstep⟩ := exists_label_step (fun n => label (path v w n)) q hp
  let i : Fin q := ⟨k,hk⟩
  have hiv : path v w k i=v i := by simp [path,i]
  have hiw : path v w (k+1) i=w i := by simp [path,i]
  have hj (j : Fin q) (hji : j ≠ i) : path v w k j=path v w (k+1) j := by
    have hh := congrFun (path_step v w i) j
    simpa only [i,Function.update_of_ne hji] using hh.symm
  have hne : v i ≠ w i := by
    intro hh
    apply hstep
    congr 1
    ext j
    by_cases hji : j=i
    · subst j; rw [hiv,hiw,hh]
    · exact hj j hji
  have hn := adjacent_of_close (v i) (w i) (x i) (z i) r (hx i) (hz i) (hc i) hr hne
  let p : Fin q → ℝ := fun j => if j=i then (max (v i) (w i):ℕ) else if j.val<k then z j else x j
  refine ⟨path v w k,path v w (k+1),i,?_,hstep,?_,?_,p,?_,?_⟩
  · exact ⟨by simpa only [hiv,hiw] using hn,hj⟩
  · intro j; simp only [path]; split_ifs <;> simp
  · intro j; simp only [path]; split_ifs <;> simp
  · constructor
    · simp [p,hiv,hiw]
    · intro j hji
      simp only [p,ite_eq_right hji,path]
      split_ifs with h
      · exact ⟨(hz j).1.le,(hz j).2.le⟩
      · exact ⟨(hx j).1.le,(hx j).2.le⟩
  · intro j
    by_cases hji : j=i
    · subst j
      simp only [p,ite_eq_left rfl]
      rcases hn with hh | hh
      · have hle : v i ≤ w i := by omega
        rw [max_eq_right hle,abs_of_nonpos (by linarith [(hz i).1] : (w i:ℝ)-z i ≤ 0)]
        have hc' := (abs_lt.mp (hc i)).1
        have he : (v i:ℝ)+1=(w i:ℝ) := by exact_mod_cast hh
        linarith [(hx i).2]
      · have hle : w i ≤ v i := by omega
        have he : (w i:ℝ)+1=(v i:ℝ) := by exact_mod_cast hh
        have hnz : 0 ≤ (v i:ℝ)-z i := by linarith [(hz i).2]
        rw [max_eq_left hle,abs_of_nonneg hnz]
        have hc' := (abs_lt.mp (hc i)).2
        linarith [(hx i).1]
    · simp only [p,ite_eq_right hji]
      split_ifs
      · simpa only [sub_self,abs_zero] using (lt_of_le_of_lt (abs_nonneg (x j-z j)) (hc j))
      · exact hc j

end
end Contingency.Grid

 

 

open Set MeasureTheory
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ}
abbrev Vertex (q K : ℕ) := Fin q → Fin K

def corner (v : Vertex q K) : Fin q → ℕ := fun i => v i

def bin (v : Vertex q K) : Interpolation.OpenBox q :=
  ⟨fun i => v i,fun i => (v i:ℝ)+1⟩

@[simp] theorem mem_bin (v : Vertex q K) (x : Fin q → ℝ) : x∈(bin v).carrier ↔ inside (corner v) x := by
  simp [bin,Interpolation.OpenBox.carrier,inside,corner]

def cube (q K : ℕ) : Interpolation.OpenBox q := ⟨fun _ => 0,fun _ => K⟩

@[simp] theorem mem_cube (x : Fin q → ℝ) : x∈(cube q K).carrier ↔ ∀ i,0<x i ∧ x i<(K:ℝ) := by
  simp [cube,Interpolation.OpenBox.carrier]

def boxes (V : Finset (Vertex q K)) : Finset (Interpolation.OpenBox q) := by classical exact V.image bin

@[simp] theorem mem_boxes (V : Finset (Vertex q K)) (x : Fin q → ℝ) :
    x∈Interpolation.boxUnion (boxes V) ↔ ∃ v∈V,inside (corner v) x := by
  classical
  simp [Interpolation.boxUnion,boxes,mem_bin]

theorem bins_subset_cube (V : Finset (Vertex q K)) : Interpolation.boxUnion (boxes V) ⊆ (cube q K).carrier := by
  intro x hx
  obtain ⟨v,_,hv⟩ := (mem_boxes V x).mp hx
  apply (mem_cube x).mpr
  intro i
  have hh : (v i:ℝ)+1 ≤ (K:ℝ) := by exact_mod_cast (v i).isLt
  exact ⟨lt_of_le_of_lt (Nat.cast_nonneg _) (hv i).1,lt_of_lt_of_le (hv i).2 hh⟩

theorem bin_unique (v w : Vertex q K) (x : Fin q → ℝ)
    (hv : inside (corner v) x) (hw : inside (corner w) x) : v=w := by
  ext i
  apply le_antisymm
  · by_contra hn
    have hn' : (w i:ℕ)+1 ≤ (v i:ℕ) := by omega
    have hh : (w i:ℝ)+1 ≤ (v i:ℝ) := by exact_mod_cast hn'
    have h1 := (hv i).1; have h2 := (hw i).2
    dsimp [corner] at h1 h2
    linarith
  · by_contra hn
    have hn' : (v i:ℕ)+1 ≤ (w i:ℕ) := by omega
    have hh : (v i:ℝ)+1 ≤ (w i:ℝ) := by exact_mod_cast hn'
    have h1 := (hw i).1; have h2 := (hv i).2
    dsimp [corner] at h1 h2
    linarith

theorem bins_disjoint : Pairwise (fun v w : Vertex q K => Disjoint (bin v).carrier (bin w).carrier) := by
  intro v w hne
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hne (bin_unique v w x ((mem_bin v x).mp hx) ((mem_bin w x).mp hy))

 
theorem ae_no_grid : ∀ᵐ x : Fin q → ℝ ∂volume,∀ i : Fin q,∀ n : ℕ,x i ≠ (n:ℝ) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro n
  exact Measure.ae_eval_ne (fun _ : Fin q => (volume : Measure ℝ)) i (n:ℝ)

theorem exists_bin (x : Fin q → ℝ) (hx : x∈(cube q K).carrier)
    (hgrid : ∀ i : Fin q,∀ n : ℕ,x i ≠ (n:ℝ)) :
    ∃ v : Vertex q K,inside (corner v) x := by
  have hc := (mem_cube x).mp hx
  have hf (i : Fin q) : ⌊x i⌋₊<K := by
    have hh := (Nat.floor_le (hc i).1.le).trans_lt (hc i).2
    exact_mod_cast hh
  let v : Vertex q K := fun i => ⟨⌊x i⌋₊,hf i⟩
  refine ⟨v,fun i => ⟨?_,?_⟩⟩
  · exact lt_of_le_of_ne (Nat.floor_le (hc i).1.le) (Ne.symm (hgrid i _))
  · exact Nat.lt_floor_add_one (x i)

theorem cube_ae_union : Interpolation.boxUnion (boxes (Finset.univ : Finset (Vertex q K))) =ᵐ[volume]
    (cube q K).carrier := by
  filter_upwards [ae_no_grid (q:=q)] with x hx
  apply propext
  constructor
  · intro hx
    exact bins_subset_cube (Finset.univ : Finset (Vertex q K)) hx
  · intro hc
    obtain ⟨v,hv⟩ := exists_bin x hc hx
    exact (mem_boxes _ x).mpr ⟨v,Finset.mem_univ _,hv⟩

def faceBox (v w : Vertex q K) (i : Fin q) (r : ℝ) : Interpolation.OpenBox q :=
  ⟨fun j => if j=i then (max (v i:ℕ) (w i:ℕ):ℕ)-r else (v j:ℝ)-r,
   fun j => if j=i then (max (v i:ℕ) (w i:ℕ):ℕ)+r else (v j:ℝ)+1+r⟩

theorem mem_faceBox (v w : Vertex q K) (i : Fin q) (r : ℝ) (p z : Fin q → ℝ)
    (hp : p∈face (corner v) (corner w) i) (hc : ∀ j,|p j-z j|<r) :
    z∈(faceBox v w i r).carrier := by
  intro j _
  have hh := abs_lt.mp (hc j)
  by_cases hj : j=i
  · subst j
    simp only [faceBox,Set.mem_Ioo,ite_true]
    have he := hp.1
    dsimp [corner] at he
    constructor <;> linarith
  · simp only [faceBox,ite_eq_right hj]
    have he := hp.2 j hj
    dsimp [corner] at he
    constructor <;> linarith

 

theorem bounded_cut_face (V : Finset (Vertex q K)) (v w : Vertex q K) (hv : v∈V) (hw : w∉V)
    (x z : Fin q → ℝ) (hx : inside (corner v) x) (hz : inside (corner w) z)
    (r : ℝ) (hr : r ≤ 1) (hc : ∀ i,|x i-z i|<r) :
    ∃ u u' : Vertex q K,∃ i : Fin q,neighbors (corner u) (corner u') i ∧
      (u∈V ∧ u'∉V ∨ u∉V ∧ u'∈V) ∧ z∈(faceBox u u' i r).carrier := by
  classical
  let lift (a : Fin q → ℕ) (ha : ∀ i,a i<K) : Vertex q K := fun i => ⟨a i,ha i⟩
  let label (a : Fin q → ℕ) : Bool := if ha : ∀ i,a i<K then decide (lift a ha∈V) else false
  have hvb : ∀ i,corner v i<K := fun i => (v i).isLt
  have hwb : ∀ i,corner w i<K := fun i => (w i).isLt
  have hl : label (corner v) ≠ label (corner w) := by simp [label,lift,corner,hv,hw]
  obtain ⟨u,u',i,hn,hl',hu,hu',p,hp,hclose⟩ := cut_face_close (corner v) (corner w) label hl x z hx hz r hr hc
  have hub : ∀ j,u j<K := fun j => by rcases hu j with h | h <;> rw [h]; exact hvb j; exact hwb j
  have hu'b : ∀ j,u' j<K := fun j => by rcases hu' j with h | h <;> rw [h]; exact hvb j; exact hwb j
  refine ⟨lift u hub,lift u' hu'b,i,hn,?_,?_⟩
  · simp only [label,dite_eq_left hub,dite_eq_left hu'b] at hl'
    by_cases h : lift u hub∈V
    · exact Or.inl ⟨h,fun h' => hl' (by simp [h,h'])⟩
    · exact Or.inr ⟨h,by by_contra h'; exact hl' (by simp [h,h'])⟩
  · exact mem_faceBox _ _ _ _ p z hp hclose

end
end Contingency.Grid

end

end OAI
