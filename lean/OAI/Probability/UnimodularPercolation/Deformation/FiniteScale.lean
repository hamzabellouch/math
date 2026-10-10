import Mathlib
import OAI.Probability.UnimodularPercolation.Escape.PathSelection

namespace OAI

/-! Deformed susceptibility, finite-scale estimates and the Riccati contradiction. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section EscapeSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

omit [Countable V] [Countable E] [Nonempty V] in
 

theorem deformed_move_of_walk (G : BondGraph V E) (hloc : LocallyFinite G)
    (a C : ℝ) (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hmove : ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b)
    (D : Set V) (b z : V) (q : (openSimpleGraph G Set.univ).Walk b z)
    (j : ℕ) (hj : q.length ≤ j) (hD : ∀ x ∈ q.support, x ∈ D) :
    Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^j *
      deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t D b := by
  obtain ⟨l,hl,he,_⟩ := walk_lift_bonds G Set.univ q
  have hlen : l.length = q.length := by
    have hh := congrArg List.length he
    simpa only [List.length_map,SimpleGraph.Walk.length_edges] using hh
  have hle : l.length ≤ j := hlen.trans_le hj
  have hcomp := hmove D b z l (hD b q.start_mem_support) hl (by
    intro e hel x hxe
    exact hD x (SimpleGraph.Walk.mem_support_of_mem_edges
      (he ▸ List.mem_map_of_mem hel) hxe))
  have he' : Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ)))) ≤
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (Real.exp_pos _).le) (neg_nonpos.mpr ht)
  have hpw : (p:ℝ)^j ≤ (p:ℝ)^l.length := pow_le_pow_of_le_one p.2.1 p.2.2 hle
  exact (mul_le_mul_of_nonneg_right (mul_le_mul he' hpw (pow_nonneg p.2.1 _) (Real.exp_pos _).le)
    (deformedSusceptibility_nonneg G _ p k t D z)).trans hcomp

 
theorem deformedSusceptibility_delete_interior (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (w : RawCorridor G k) (x : V) :
    deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x -
      maxSusceptibility G p * (∑ z ∈ w.neighborhood hloc, twoPoint G p x z) ≤
      deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ x := by
  have hh := deformedSusceptibility_deletion G hloc hqt _ hP p hp k t ht Set.univ (w.interior : Set V) x
  rw [←w.coe_neighborhood hloc,Finset.tsum_subtype'] at hh
  have he : Set.univ \ (w.interior : Set V) = (w.interior : Set V)ᶜ := by ext z; simp
  rw [he] at hh
  exact hh

 

theorem selected_retained_product_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (j : ℕ) (s C cf χ : ℝ) (hcf : 0 ≤ cf) (hχ : 0 ≤ χ)
    (hrow : ∀ x, cf*χ ≤ deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x)
    (hcost : maxSusceptibility G p*s ≤ (cf/2)*χ)
    (hmove : ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b)
    (w : RawCorridor G k) (hw : w.Selected hloc p j s) :
    Real.exp (-2*t*(j:ℝ)*Real.exp (C*(k:ℝ))) * (p:ℝ)^(2*j) * ((cf/2)*χ)^2 ≤
      retainedSusceptibilityProduct G (walkKernel G hloc a) p t w := by
  have hx (x : V) (he : w.HasEscape hloc p j s x) :
      Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ))))*(p:ℝ)^j*((cf/2)*χ) ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ x := by
    obtain ⟨z,q,_hq,hj,havoid,hs⟩ := he
    have hd := deformedSusceptibility_delete_interior G hloc hqt a hP p hp k t ht w z
    have hδ : (cf/2)*χ ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t (w.interior : Set V)ᶜ z := by
      have hb := mul_le_mul_of_nonneg_left hs (zero_le_one.trans (maxSusceptibility_one_le G hloc hqt p hp))
      have hr := hrow z
      linarith
    exact (mul_le_mul_of_nonneg_left hδ
      (mul_nonneg (Real.exp_pos _).le (pow_nonneg p.2.1 _))).trans
        (deformed_move_of_walk G hloc a C p k t ht hmove (w.interior : Set V)ᶜ x z q j hj havoid)
  have h₁ := hx w.base hw.2.1
  have h₂ := hx w.endpoint hw.2.2
  have hfactor : 0 ≤ Real.exp (-t*((j:ℝ)*Real.exp (C*(k:ℝ))))*(p:ℝ)^j*((cf/2)*χ) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg p.2.1 _))
      (mul_nonneg (div_nonneg hcf (by norm_num)) hχ)
  have hh := mul_le_mul h₁ h₂ hfactor
    (deformedSusceptibility_nonneg G _ p k t (w.interior : Set V)ᶜ w.base)
  rw [retainedSusceptibilityProduct,ite_eq_left hw.1]
  apply le_trans (le_of_eq ?_) hh
  have he : -2*t*(j:ℝ)*Real.exp (C*(k:ℝ)) =
      -t*((j:ℝ)*Real.exp (C*(k:ℝ))) + -t*((j:ℝ)*Real.exp (C*(k:ℝ))) := by ring
  rw [he,Real.exp_add,show 2*j=j+j by omega,pow_add]
  ring

end EscapeSusceptibility
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedRetention
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

omit [Countable V] [Countable E] [Nonempty V] in
theorem averagedDeformedSusceptibility_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (t : ℝ) :
    0 ≤ averagedDeformedSusceptibility G P p k root weight t :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (deformedSusceptibility_nonneg G P p k t Set.univ (root i)))

omit [Countable V] [Countable E] [Nonempty V] in
theorem deformedKernel_symm (G : BondGraph V E) (P : V → V → ℝ)
    (p : unitInterval) (k : ℕ) (t : ℝ) (D : Set V) (x y : V) :
    deformedKernel G P p k t D x y = deformedKernel G P p k t D y x := by
  simp only [deformedKernel,deformedConnection_symm G P p k t D _ x y]

omit [Nonempty V] in
 

theorem deformed_row_le_root_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (p : unitInterval) (k : ℕ) (t : ℝ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (x : V) :
    deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ x ≤
      c*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
  obtain ⟨i,g,⟨e,he⟩,rfl⟩ := hcov x
  rw [deformedSusceptibility_aut G he _ (walkKernel_covariant G hloc a he)]
  simp only [Set.preimage_univ]
  have hs := deformedSusceptibility_nonneg G (walkKernel G hloc a) p k t Set.univ
  have hi := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun r => weight r * deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root r))
    (fun r _ => mul_nonneg (hw r) (hs (root r))) (Finset.mem_univ i)
  have hi' := mul_le_mul_of_nonneg_left hi hc
  have hh := mul_le_mul_of_nonneg_right (hmin i) (hs (root i))
  change _ ≤ c*∑ r, weight r * deformedSusceptibility G (walkKernel G hloc a) p k t Set.univ (root r)
  nlinarith

 

theorem deformed_norm_le_root_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (a : ℝ) (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (p : unitInterval) (hp : p < pc G) (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (B : Hilbert V →L[ℂ] Hilbert V)
    (hB : ∀ x y, matrixCoeff B x y = (deformedKernel G (walkKernel G hloc a) p k t Set.univ x y : ℂ)) :
    ‖B‖ ≤ c*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
  have hs (x : V) (F : Finset V) :
      (∑ y ∈ F, |deformedKernel G (walkKernel G hloc a) p k t Set.univ x y|) ≤
        c*averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
    simp only [abs_of_nonneg (deformedKernel_nonneg G _ p k t _ _ _)]
    exact ((summable_deformedKernel G hloc hqt _ hP p hp k t ht Set.univ x).sum_le_tsum F
      (fun y _ => deformedKernel_nonneg G _ p k t _ x y)).trans
        (deformed_row_le_root_sum G hloc a p k t root weight hw hcov c hc hmin x)
  exact operator_norm_le_absolute_sums _ _
    (mul_nonneg hc (averagedDeformedSusceptibility_nonneg G _ p k root weight hw t)) hs
    (fun y F => by simpa only [deformedKernel_symm G _ p k t Set.univ] using hs y F) B hB

 

theorem deformed_root_sum_retained (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hA : HasKernel G p A) (k : ℕ) (t B : ℝ) (ht : 0 ≤ t)
    (htB : t*‖A‖ ≤ B) (hB : B*‖P‖^k ≤ 1/4) :
    ‖A‖/(2*c) ≤ averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  obtain ⟨T,hT,_,_,hret⟩ := exists_deformedOperator_small_change G hG hloc p hp0
    ((show (p:ℝ)<(pc G:ℝ) from hp).trans_le (pc G).2.2) a P hpos hPs hP
    A (hA.positiveRealMatrix G p A) (hA.isPositive G p A).isSelfAdjoint hA k t ht
  have hn := deformed_norm_le_root_sum G hloc hqt a hK p hp k t ht root weight hw hcov c hc.le hmin T hT
  have hsmall := (mul_le_mul_of_nonneg_right htB (pow_nonneg (norm_nonneg P) k)).trans hB
  have hh := mul_le_mul_of_nonneg_right hsmall (norm_nonneg A)
  apply (div_le_iff₀ (by positivity : 0 < 2*c)).mpr
  nlinarith

end AveragedRetention
end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section AveragePositiveTerm
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

omit [Countable V] [Countable E] [Nonempty V] in
 
theorem selected_average_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ) (t : ℝ)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (j : ℕ) (s b F : ℝ) (hF : 0 ≤ F)
    (hm : b ≤ rawPathAverage G P k root weight
      (fun w => if w.Selected hloc p j s then 1 else 0))
    (hgood : ∀ w : RawCorridor G k, w.Selected hloc p j s →
      F ≤ retainedSusceptibilityProduct G P p t w) :
    F*b ≤ rawPathAverage G P k root weight (retainedSusceptibilityProduct G P p t) := by
  have hh := rawPathAverage_mono G hloc P hP k root weight hw
    (fun w => F*(if w.Selected hloc p j s then 1 else 0))
    (retainedSusceptibilityProduct G P p t) (by
      intro w
      by_cases hs : w.Selected hloc p j s
      · simpa only [hs,ite_true,mul_one] using hgood w hs
      · simp only [hs,ite_false,mul_zero,retainedSusceptibilityProduct]
        split_ifs
        · exact mul_nonneg (deformedSusceptibility_nonneg G P p k t _ w.base)
            (deformedSusceptibility_nonneg G P p k t _ w.endpoint)
        · exact le_rfl)
  rw [rawPathAverage_const_mul] at hh
  exact (mul_le_mul_of_nonneg_left hm hF).trans hh
end AveragePositiveTerm

section RiccatiContradiction
 

theorem riccati_retention_bound (χ D : ℝ → ℝ) (T m c h : ℝ)
    (hT : 0 < T) (hm : 0 < m) (hc : 0 < c) (_hh : 0 ≤ h)
    (hret : ∀ t ∈ Set.Icc (T/2) T, m/(2*c) ≤ χ t)
    (hder : ∀ t ∈ Set.Icc (T/2) T, HasDerivAt χ (-D t) t)
    (hdec : ∀ t ∈ Set.Icc (T/2) T, h*(χ t)^2 ≤ D t) :
    h*T*m ≤ 4*c := by
  have hpos (t) (ht : t ∈ Set.Icc (T/2) T) : 0 < χ t :=
    (div_pos hm (by positivity)).trans_le (hret t ht)
  have hd (t) (ht : t ∈ Set.Icc (T/2) T) :
      HasDerivAt (fun s => (χ s)⁻¹) (D t/(χ t)^2) t := by
    convert! (hder t ht).inv (hpos t ht).ne' using 1
    simp only [neg_neg]
  have hcχ : ContinuousOn (fun s => (χ s)⁻¹) (Set.Icc (T/2) T) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => (χ s)⁻¹) (interior (Set.Icc (T/2) T)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hdl (t) (ht : t ∈ interior (Set.Icc (T/2) T)) :
      h ≤ deriv (fun s => (χ s)⁻¹) t := by
    rw [(hd t (interior_subset ht)).deriv]
    exact (le_div_iff₀ (sq_pos_of_pos (hpos t (interior_subset ht)))).mpr (hdec t (interior_subset ht))
  have hs := (convex_Icc (T/2) T).mul_sub_le_image_sub_of_le_deriv hcχ hdiff hdl
    (T/2) ⟨le_rfl,by linarith⟩ T ⟨by linarith,le_rfl⟩ (by linarith)
  have hstart : 0 ≤ (χ (T/2))⁻¹ := (inv_pos.mpr (hpos _ ⟨le_rfl,by linarith⟩)).le
  have hend : (χ T)⁻¹ ≤ 2*c/m := by
    have hb := one_div_le_one_div_of_le (div_pos hm (by positivity)) (hret T ⟨by linarith,le_rfl⟩)
    simpa only [one_div,inv_div] using hb
  have hs' : h*(T/2) ≤ 2*c/m := by linarith
  have hs'' := (le_div_iff₀ hm).mp hs'
  nlinarith
end RiccatiContradiction
end Percolation

 

 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteScale
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Infinite V]
variable {ι : Type*} [Fintype ι]

 

theorem exists_finite_scale_obstruction
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (A : Hilbert V →L[ℂ] Hilbert V), HasKernel G p A →
      ∀ k : ℕ, k₀ ≤ k → ∀ B : ℝ, 0 < B →
      let R := maxSusceptibility G p/‖A‖
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
      B*‖P‖^k ≤ 1/4 →
      B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ ‖A‖ →
      R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*((pc G:ℝ)/2)^(2*j) →
      M < B*((pc G:ℝ)/2)^(2*j) → False := by
  have hK (x y : V) : 0 ≤ walkKernel G hloc a x y := by
    simpa only [hP,Complex.ofReal_re] using (hpos x y).2
  have hw₀ (i) := (hw i).le
  obtain ⟨Cr,cf,hCr,hcf,hrow⟩ := exists_uniform_deformed_row_comparison G hconn hloc hqt
    root weight hw₀ hw1 (fun x => by
      obtain ⟨i,g,⟨e,he⟩,hx⟩ := hcov x
      exact ⟨i,g,e,he,hx⟩) d hd a hK hpcrit hpcrit₁
  obtain ⟨Cm,hCm,hmove⟩ := exists_uniform_deformed_endpoint_comparison G hloc hqt d hd a hK hpcrit hpcrit₁
  obtain ⟨Cd,hCd,hdecrease⟩ := exists_uniform_averaged_decrease G hG hloc hqt
    root weight hw₀ (vertexAut G) (Set.Subset.refl _) htr d hd a hK hpcrit hpcrit₁ P hpos hP hsym
  let τ := cf/(8*c)
  have hτ : 0 < τ := div_pos hcf (by positivity)
  obtain ⟨J,C₁,k₀,b,hJ,hC₁,hk₀,hb,hselected⟩ := exists_selected_path_mass G hconn hloc hqt
    a ha root weight htr hcov hw hw1 c hc hmin P hpos hsym hP hdiag hρ d hd τ hτ
  let C := Cr+Cm+Cd
  let q := b*Real.exp (-2)*(cf/2)^2
  let H := (1+2*(d:ℝ)/(pc G:ℝ))*(2*c)^2
  let ε := q/(2*H)
  let h₀ := Real.exp (-1)*q/2
  let M := 4*c/h₀
  have hq : 0 < q := by dsimp [q]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hε : 0 < ε := div_pos hq (by positivity)
  have hh₀ : 0 < h₀ := by dsimp [h₀]; positivity
  have hM : 0 < M := div_pos (by positivity) hh₀
  refine ⟨C,by dsimp [C]; positivity,J,hJ,C₁,hC₁,k₀,hk₀,ε,M,hε,hM,?_⟩
  intro p hpnear hp A hA k hk B hB
  dsimp only
  let m := ‖A‖
  let R := maxSusceptibility G p/m
  let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
  let β := ((pc G:ℝ)/2)^(2*j)
  let T := B/m
  let χ := averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight
  let D := fun t => ∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p
  change B*‖P‖^k ≤ 1/4 → B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ m →
    R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*β → M < B*β → False
  intro hsmall htime herrscale hlarge
  have hm : 0 < m := zero_lt_one.trans_le (hA.norm_one_le G p A)
  have hR : 1 ≤ R := (one_le_div hm).mpr (hA.norm_le_maxSusceptibility G hloc hqt p hp A)
  have hβ : 0 < β := pow_pos (half_pos hpcrit) _
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjr : (1:ℝ) ≤ (j:ℝ) := Nat.one_le_cast.mpr hj
  have hk3 : 3 ≤ k := hk₀.trans hk
  have hpzero : 0 < (p:ℝ) := (half_pos hpcrit).trans_le hpnear
  have hT : 0 < T := div_pos hB hm
  have hTb (t : ℝ) (ht : t ≤ T) : t*m ≤ B := (le_div_iff₀ hm).mp ht
  have htim (t : ℝ) (ht : t ≤ T) : t*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ 1 := by
    have hm' := mul_le_mul_of_nonneg_right (hTb t ht)
      (mul_nonneg (Nat.cast_nonneg j) (Real.exp_pos (C*(k:ℝ))).le)
    nlinarith only [hm',htime,hm]
  have hCbound (C' : ℝ) (hC' : C' ≤ C) : Real.exp (C'*(k:ℝ)) ≤ Real.exp (C*(k:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC' (Nat.cast_nonneg k))
  have htim' (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (C' : ℝ) (hC' : C' ≤ C) :
      t*Real.exp (C'*(k:ℝ)) ≤ 1 := by
    have he := mul_le_mul_of_nonneg_left (hCbound C' hC') ht
    have hj' := mul_le_mul_of_nonneg_left hjr (mul_nonneg ht (Real.exp_pos (C*(k:ℝ))).le)
    nlinarith only [he,hj',htim t htT]
  have hret (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) : m/(2*c) ≤ χ t :=
    deformed_root_sum_retained G hG hloc hqt a p hpzero hp root weight hw₀ hcov c hc hmin
      P A hpos hsym hP hA k t B ht (hTb t htT) hsmall
  have hdec (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) : (h₀*β)*(χ t)^2 ≤ D t := by
    have hχ : 0 ≤ χ t := averagedDeformedSusceptibility_nonneg G _ p k root weight hw₀ t
    have hret' := (div_le_iff₀ (by positivity : 0 < 2*c)).mp (hret t ht htT)
    have hrow' := hrow p hpnear hp k hk3 t ht (htim' t ht htT Cr (by dsimp [C]; linarith only [hCr,hCm,hCd]))
    have hcost : maxSusceptibility G p*(τ/R) ≤ (cf/2)*χ t := by
      have hmax : maxSusceptibility G p ≠ 0 :=
        (zero_lt_one.trans_le (maxSusceptibility_one_le G hloc hqt p hp)).ne'
      have he : maxSusceptibility G p*(τ/R) = τ*m := by dsimp [R]; field_simp [hmax]
      rw [he]
      have hh := mul_le_mul_of_nonneg_left hret' hτ.le
      have hτcf : τ*(2*c) = cf/4 := by dsimp [τ]; field_simp; ring
      rw [mul_left_comm τ (χ t) (2*c),hτcf,mul_comm (χ t)] at hh
      nlinarith only [hh,hcf,hχ]
    have hprod (w : RawCorridor G k) (hwsel : w.Selected hloc p j (τ/R)) :
        Real.exp (-2)*β*((cf/2)*χ t)^2 ≤ retainedSusceptibilityProduct G (walkKernel G hloc a) p t w := by
      have hbnd := selected_retained_product_lower G hloc hqt a hK p hp k t ht j (τ/R) Cm cf (χ t)
        hcf.le hχ hrow' hcost (hmove p hpnear hp k hk3 t ht) w hwsel
      have he : Real.exp (-2) ≤ Real.exp (-2*t*(j:ℝ)*Real.exp (Cm*(k:ℝ))) := by
        apply Real.exp_le_exp.mpr
        have he' := mul_le_mul_of_nonneg_left (hCbound Cm (by dsimp [C]; linarith only [hCr,hCm,hCd]))
          (mul_nonneg ht (Nat.cast_nonneg j))
        linarith only [he',htim t htT]
      have hpw : β ≤ (p:ℝ)^(2*j) := pow_le_pow_left₀ (half_pos hpcrit).le hpnear _
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul he hpw hβ.le (Real.exp_pos _).le) (sq_nonneg _)).trans hbnd
    have hsel := hselected p hpnear hp k hk R hR
    have hpositive := selected_average_lower G hloc _ hK p k t root weight hw₀ j (τ/R) b
      (Real.exp (-2)*β*((cf/2)*χ t)^2) (by positivity) hsel hprod
    have hpositive' : q*β*(χ t)^2 ≤ rawPathAverage G (walkKernel G hloc a) k root weight
        (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) := by
      convert hpositive using 1
      dsimp [q]
      ring
    have ha₃ : 0 ≤ rootTriangle G root weight (p:ℝ) :=
      zero_le_one.trans (rootTriangle_one_le G hloc hqt root weight hw₀ hw1 p hp)
    have herror : (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
        (‖P‖^k*(rootTrace root weight (A^3)).re) ≤ (q/2)*β*(χ t)^2 := by
      rw [←rootTriangle_eq_trace G p root weight A hA]
      have hx : maxSusceptibility G p = R*m := by dsimp [R]; field_simp
      rw [hx]
      have hcoeff : 0 ≤ (1+2*(d:ℝ)/(pc G:ℝ)) := by positivity
      have hm2 : m^2 ≤ (2*c)^2*(χ t)^2 := by
        calc
          m^2 ≤ (χ t*(2*c))^2 := pow_le_pow_left₀ hm.le hret' 2
          _ = _ := by ring
      have h₁ := mul_le_mul_of_nonneg_left hm2
        (mul_nonneg (mul_nonneg hcoeff (sq_nonneg R)) (mul_nonneg ha₃ (pow_nonneg (norm_nonneg P) k)))
      have h₂ := mul_le_mul_of_nonneg_left herrscale (mul_nonneg hH.le (sq_nonneg (χ t)))
      have he : H*ε = q/2 := by dsimp [ε]; field_simp
      calc
        _ ≤ H*(R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k)*(χ t)^2 := by dsimp [H]; nlinarith only [h₁]
        _ ≤ H*(ε*β)*(χ t)^2 := by nlinarith only [h₂]
        _ = _ := by rw [←mul_assoc H ε β,he]
    have hdiff : (q/2)*β*(χ t)^2 ≤
        rawPathAverage G (walkKernel G hloc a) k root weight
          (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
          (‖P‖^k*(rootTrace root weight (A^3)).re) := by linarith only [hpositive',herror]
    have hexp : Real.exp (-1) ≤ Real.exp (-t*Real.exp (Cd*(k:ℝ))) :=
      Real.exp_le_exp.mpr (by linarith only [htim' t ht htT Cd (by dsimp [C]; linarith only [hCr,hCm]) ])
    have hh := mul_le_mul hexp hdiff (by positivity) (Real.exp_pos _).le
    have hdecr := hdecrease p hpnear hp A hA k hk3 t ht
    apply le_trans _ hdecr
    convert hh using 1
    dsimp [h₀]
    ring
  have hb := riccati_retention_bound χ D T m c (h₀*β) hT hm hc (mul_pos hh₀ hβ).le
    (fun t ht => hret t (by linarith only [ht.1,hT]) ht.2)
    (fun t ht => hasDerivAt_averagedDeformedSusceptibility G hloc hqt root weight d hd a hK p hpzero hp k t
      (by linarith only [ht.1,hT]))
    (fun t ht => hdec t (by linarith only [ht.1,hT]) ht.2)
  have he : h₀*β*T*m = h₀*(B*β) := by dsimp [T]; field_simp
  rw [he] at hb
  have hg := (div_lt_iff₀ hh₀).mp hlarge
  nlinarith only [hg,hb]

end FiniteScale
end Percolation

end OAI
