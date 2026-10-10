import Mathlib.Algebra.Star.UnitaryStarAlgAut
import OAI.Analysis.FactorGeneration.SpectralDimension

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_add_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx+
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  classical
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herrQ⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/4) (by positivity)
  obtain ⟨R,d,_,hR,herrR⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ y hy (ε/4) (by positivity)
  simp only [one_mul,mul_one] at herrQ herrR
  have hQx := hQ x (Commute.refl x) (Commute.one_left x)
  have hQy := hQ y hxy (Commute.one_left y)
  have hRx := hR x hxy.symm (Commute.one_left x)
  have hRy := hR y (Commute.refl y) (Commute.one_left y)
  have hc (i : Fin Q.size) (j : Fin R.size) :
      Commute (Q.piece i).val (R.piece j).val :=
    (hR _ (hQy i).symm (Commute.one_left _) j).symm
  let q := Q.jointPiece R hc
  let b (a : Fin Q.size × Fin R.size) : ℂ := (c a.1 : ℂ)+(d a.2 : ℂ)
  let sx : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
  let sy : M.toStarSubalgebra := ∑ j, (d j : ℂ) • (R.piece j).val
  let wx : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  let wy : ℂ := ∑ j, (d j : ℂ)*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)
  have hsum : (∑ a, b a • (q a).val)=sx+sy := by
    simp only [b,add_smul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (Q.joint_sum_left R hc (fun i => (c i : ℂ)))
      (Q.joint_sum_right R hc (fun j => (d j : ℂ)))
  have hweight : (∑ a, b a*(traceFreeDimension hfactor hdiff (q a) : ℂ))=wx+wy := by
    simp only [b,add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·)
      (Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit (fun i => (c i : ℂ)))
      (Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit (fun j => (d j : ℂ)))
  have hcomm (a : Fin Q.size × Fin R.size) : Commute (q a).val (x+y) :=
    ((hQx a.1).mul_left (hRx a.2)).add_right ((hQy a.1).mul_left (hRy a.2))
  have hz := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (x+y) (hx.add hy)).2.family_bound
    hfactor hdiff q (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc) b hcomm
  rw [hsum,hweight] at hz
  have he : ‖(x+y)-(sx+sy)‖ ≤ ‖x-sx‖+‖y-sy‖ := by
    rw [show (x+y)-(sx+sy)=(x-sx)+(y-sy) by abel]
    exact norm_add_le _ _
  have hxv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hQx
  have hyv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit y hy).2
    R (fun j => (d j : ℂ)) hRy
  let vx := dimensionSpectralValue hfactor hdiff hfinite hunit x hx
  let vy := dimensionSpectralValue hfactor hdiff hfinite hunit y hy
  have hv : ‖(vx+vy)-(wx+wy)‖ ≤ ‖vx-wx‖+‖vy-wy‖ := by
    rw [show (vx+vy)-(wx+wy)=(vx-wx)+(vy-wy) by abel]
    exact norm_add_le _ _
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)) (wx+wy) (vx+vy)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (wx+wy) (vx+vy)] at htri
  change ‖vx-wx‖ ≤ ‖x-sx‖ at hxv
  change ‖vy-wy‖ ≤ ‖y-sy‖ at hyv
  change ‖x-sx‖ < ε/4 at herrQ
  change ‖y-sy‖ < ε/4 at herrR
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)-(vx+vy)‖ ≤ 0+ε
  linarith

theorem dimensionSpectralValue_sub_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x-y) (hx.sub hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx-
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  simpa only [sub_eq_add_neg,dimensionSpectralValue_neg hfactor hdiff hfinite hunit y hy] using
    dimensionSpectralValue_add_of_commute hfactor hdiff hfinite hunit x (-y) hx hy.neg hxy.neg_right

theorem dimensionSpectralValue_sub_norm_le_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    ‖dimensionSpectralValue hfactor hdiff hfinite hunit x hx-
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy‖ ≤ ‖x-y‖ := by
  rw [← dimensionSpectralValue_sub_of_commute hfactor hdiff hfinite hunit x y hx hy hxy]
  exact dimensionSpectralValue_norm_le hfactor hdiff hfinite hunit (x-y) (hx.sub hy)

end

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralValueCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralValueOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralValuePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralValueLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralValueStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

namespace SpectralInterval
variable {x : M.toStarSubalgebra} (I : SpectralInterval x) (hx : IsSelfAdjoint x)

theorem child_endpoints (hI : I.lo ≤ I.hi) (b : Bool) :
    I.lo ≤ (I.child hx b).lo ∧ (I.child hx b).lo ≤ (I.child hx b).hi ∧
      (I.child hx b).hi ≤ I.hi := by
  cases b <;> dsimp [child,low,high,midpoint]
  · exact ⟨le_rfl,by linarith,by linarith⟩
  · exact ⟨by linarith,by linarith,le_rfl⟩

theorem level_endpoints (hI : I.lo ≤ I.hi) : ∀ n i,
    I.lo ≤ (I.level hx n i).lo ∧ (I.level hx n i).lo ≤ (I.level hx n i).hi ∧
      (I.level hx n i).hi ≤ I.hi
  | 0,_ => ⟨le_rfl,hI,le_rfl⟩
  | n+1,i => by
    have h := level_endpoints hI n i.1
    have hchild := (I.level hx n i.1).child_endpoints hx h.2.1 i.2
    exact ⟨h.1.trans hchild.1,hchild.2.1,hchild.2.2.trans h.2.2⟩

end SpectralInterval

/-- A positive operator has arbitrarily accurate finite positive spectral
approximants preserving its entire commutant. -/
theorem exists_positive_spectral_approximation
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (c : Fin Q.size → ℝ),
      (∀ i, 0 ≤ c i) ∧
      (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
      ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I : SpectralInterval x :=
    { proj := ⟨1,IsStarProjection.one _⟩
      lo := 0
      hi := ‖x‖
      lower := by simpa only [one_mul,mul_one,Complex.ofReal_zero,zero_smul,sub_zero] using hx
      upper := (initialSpectralInterval ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint).upper }
  have hI : I.lo ≤ I.hi := norm_nonneg x
  obtain ⟨n,hn⟩ := I.exists_approximant hx.isSelfAdjoint hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx.isSelfAdjoint n,fun i => (I.level hx.isSelfAdjoint n (e i)).lo,?_,?_,?_⟩
  · intro i
    exact (I.level_endpoints hx.isSelfAdjoint hI n (e i)).1
  · intro y hy i
    exact I.partition_commutes hx.isSelfAdjoint hy (Commute.one_left y) n i
  · change ‖x-∑ i, ((I.level hx.isSelfAdjoint n (e i)).lo : ℂ) •
        (I.level hx.isSelfAdjoint n (e i)).proj.val‖ < ε
    rw [Equiv.sum_comp e (fun i => ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val)]
    change ‖1*x*1-∑ i, ((I.level hx.isSelfAdjoint n i).lo : ℂ) •
      (I.level hx.isSelfAdjoint n i).proj.val‖ < ε at hn
    simpa only [one_mul,mul_one] using hn

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_spectral_approximation x hx ε hε
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2
    Q (fun i => (c i : ℂ)) (hQ x (Commute.refl x))
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
  have hw : 0 ≤ w := Finset.sum_nonneg (fun i _ => mul_nonneg (hc i)
    (traceFreeDimension_nonneg hfactor hdiff _))
  have he : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
  have hb : ‖t-(w : ℂ)‖ < ε := by rw [he]; exact hval.trans_lt herr
  have hre := Complex.re_le_norm ((w : ℂ)-t)
  rw [Complex.sub_re,Complex.ofReal_re,norm_sub_rev (w : ℂ) t] at hre
  change 0 ≤ t.re+ε
  linarith

theorem dimensionSpectralValue_mono_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) (hle : x ≤ y) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).re ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit y hy).re := by
  have h := dimensionSpectralValue_nonneg hfactor hdiff hfinite hunit (y-x) (sub_nonneg.mpr hle)
  rw [dimensionSpectralValue_sub_of_commute hfactor hdiff hfinite hunit y x hy hx hxy.symm,
    Complex.sub_re] at h
  exact sub_nonneg.mp h

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralFaithfulCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralFaithfulOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralFaithfulPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralFaithfulLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralFaithfulStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem positive_spectral_cut_domination
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    (t : ℂ) • (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≤ x := by
  let p : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩
  let q := cornerSpectralCut p x t
  have hl : 0 ≤ q.val*x*q.val-(t : ℂ) • q.val := cornerSpectralCut_lower p x hx.isSelfAdjoint t
  have hr := star_left_conjugate_nonneg hx (1-q.val)
  rw [star_sub,star_one,q.property.isSelfAdjoint.star_eq] at hr
  have hsum := add_nonneg hl hr
  have he := cornerSpectralPartition_pinch p x hx.isSelfAdjoint t
  rw [cornerSpectralPartition,CornerPartition.binary_pinch] at he
  change q.val*x*q.val+(1-q.val)*x*(1-q.val)=1*x*1 at he
  simp only [one_mul,mul_one] at he
  have he' : q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=x-(t : ℂ) • q.val := by
    rw [show q.val*x*q.val-(t : ℂ) • q.val+(1-q.val)*x*(1-q.val)=
      (q.val*x*q.val+(1-q.val)*x*(1-q.val))-(t : ℂ) • q.val by abel,he]
  rw [he'] at hsum
  exact sub_nonneg.mp hsum

theorem positive_spectral_cut_ne_zero
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) (ht : 0 ≤ t) (htx : t < ‖x‖) :
    (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t).val ≠ 0 := by
  intro hz
  have h := cornerSpectralCut_upper ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  dsimp only at h
  rw [hz,sub_zero,one_mul,mul_one] at h
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_nonpos.mp h) hx
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg ht] at hn
  have hone := (IsStarProjection.one M.toStarSubalgebra).norm_le
  have hb : ‖x‖ ≤ t := hn.trans (by nlinarith)
  exact (not_lt_of_ge hb) htx

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_spectral_cut_lower
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    t*traceFreeDimension hfactor hdiff (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t) ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x t
  have hq : Commute q.val x := by
    show q.val*x=x*q.val
    simpa only [one_mul,mul_one] using cornerSpectralCut_commutes
      ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  have htq : Commute (t • q.val) x := by
    show (t • q.val)*x=x*(t • q.val)
    rw [smul_mul_assoc,mul_smul_comm,hq.eq]
  have hle : t • q.val ≤ x := by
    simpa only [Complex.coe_smul] using positive_spectral_cut_domination x hx t
  have h := dimensionSpectralValue_mono_of_commute hfactor hdiff hfinite hunit
    (t • q.val) x ((IsSelfAdjoint.all t).smul q.property.isSelfAdjoint) hx.isSelfAdjoint htq hle
  rw [dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit t q.val q.property.isSelfAdjoint,
    dimensionSpectralValue_projection hfactor hdiff hfinite hunit q,
    ← Complex.ofReal_mul,Complex.ofReal_re] at h
  exact h

theorem dimensionSpectralValue_pos
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hx0 : x≠0) :
    0 < (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x (‖x‖/2)
  have hq : q.val≠0 := positive_spectral_cut_ne_zero x hx (‖x‖/2) (by positivity) (by linarith)
  have hd : 0 < traceFreeDimension hfactor hdiff q := traceFreeDyadicSup_pos
    hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q hq
  exact (mul_pos (half_pos hn) hd).trans_le
    (dimensionSpectralValue_spectral_cut_lower hfactor hdiff hfinite hunit x hx (‖x‖/2))

theorem dimensionSpectralValue_eq_zero_iff_of_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint=0 ↔ x=0 := by
  constructor
  · intro h
    by_contra hx0
    have hp := dimensionSpectralValue_pos hfactor hdiff hfinite hunit x hx hx0
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  · intro h
    subst x
    exact dimensionSpectralValue_zero hfactor hdiff hfinite hunit

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def AlgebraProjection.unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u p.val,
    p.property.map (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u)⟩

theorem AlgebraProjection.equivalent_unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) : p.Equivalent (p.unitaryConjugate u) := by
  let v : PartialIsometry M :=
    { support := p
      val := (u : M.toStarSubalgebra)*p.val
      initial := by
        simp only [star_mul,p.property.isSelfAdjoint.star_eq]
        rw [mul_assoc,← mul_assoc (star (u : M.toStarSubalgebra)),
          Unitary.star_mul_self_of_mem u.property,one_mul,p.property.isIdempotentElem.eq] }
  refine ⟨v,rfl,?_⟩
  apply Subtype.ext
  change ((u : M.toStarSubalgebra)*p.val)*star ((u : M.toStarSubalgebra)*p.val)=
    (u : M.toStarSubalgebra)*p.val*star (u : M.toStarSubalgebra)
  simp only [star_mul,p.property.isSelfAdjoint.star_eq,mul_assoc]
  rw [← mul_assoc p.val,p.property.isIdempotentElem.eq]

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_unitaryConjugate (p : AlgebraProjection M)
    (u : unitary M.toStarSubalgebra) :
    traceFreeDimension hfactor hdiff (p.unitaryConjugate u)=traceFreeDimension hfactor hdiff p :=
  (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
    (p.equivalent_unitaryConjugate u)).symm

theorem dimensionSpectralValue_unitary_conjugate
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (u : unitary M.toStarSubalgebra) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit
      (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u x)
      (hx.map (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u))=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u
  have hnorm (a : M.toStarSubalgebra) : ‖φ a‖=‖a‖ := by
    change ‖((u : M.toStarSubalgebra)*a)*(star u : unitary M.toStarSubalgebra)‖=‖a‖
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/2) (half_pos hε)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  let q (i : Fin Q.size) := (Q.piece i).unitaryConjugate u
  have ho (i j : Fin Q.size) (hij : i≠j) : (q i).val*(q j).val=0 := by
    change φ (Q.piece i).val*φ (Q.piece j).val=0
    exact (map_mul φ (Q.piece i).val (Q.piece j).val).symm.trans
      ((congrArg φ (Q.orthogonal i j hij)).trans (map_zero φ))
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    change (∑ i, φ (Q.piece i).val)=1
    exact (map_sum φ (fun i => (Q.piece i).val) Finset.univ).symm.trans
      ((congrArg φ Q.total).trans (map_one φ))
  have hcomm (i : Fin Q.size) : Commute (q i).val (φ x) :=
    (hc i).map φ
  have hmap : (∑ i, (c i : ℂ) • (q i).val)=φ (∑ i, (c i : ℂ) • (Q.piece i).val) := by
    change (∑ i, (c i : ℂ) • φ (Q.piece i).val)=_
    simp only [map_sum,map_smul]
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (φ x) (hx.map φ)).2.family_bound
    hfactor hdiff q ho hs (fun i => (c i : ℂ)) hcomm
  have hweight : (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (q i) : ℂ))=
      ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [q,traceFreeDimension_unitaryConjugate hfactor hdiff]
  have hval' :
      ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
        ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x - ∑ i, (c i : ℂ) • (Q.piece i).val‖ := by
    calc
      _ = ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
          ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (q i) : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖dimensionSpectralValue hfactor hdiff hfinite hunit
          (φ x) (hx.map φ) - z‖) hweight.symm
      _ ≤ ‖φ x - ∑ i, (c i : ℂ) • (q i).val‖ := hval
      _ = ‖φ (x - ∑ i, (c i : ℂ) • (Q.piece i).val)‖ :=
        congrArg (fun z : M.toStarSubalgebra => ‖z‖)
          ((congrArg (fun z => φ x - z) hmap).trans (map_sub φ x _).symm)
      _ = _ := hnorm _
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ))
    (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)] at htri
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ)-
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ 0+ε
  linarith only [htri,hval',hxval,herr]

end

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralSquareCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralSquareOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralSquareStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_star_mul_self
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (star x*x) (IsSelfAdjoint.star_mul_self x)=
      dimensionSpectralValue hfactor hdiff hfinite hunit (x*star x) (IsSelfAdjoint.mul_star_self x) := by
  obtain ⟨u,hu⟩ := exists_unitary_polar_decomposition hfactor hfinite x
  let a := CFC.sqrt (star x*x)
  have ha : star a=a := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have haa : a*a=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)
  have he : Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u (star x*x)=x*star x := by
    change (u : M.toStarSubalgebra)*(star x*x)*star (u : M.toStarSubalgebra)=x*star x
    calc _ = ((u : M.toStarSubalgebra)*a)*star ((u : M.toStarSubalgebra)*a) := by
           rw [star_mul,ha,← haa]
           simp only [mul_assoc]
      _ = x*star x := by rw [hu]
  have h := dimensionSpectralValue_unitary_conjugate hfactor hdiff hfinite hunit
    u (star x*x) (IsSelfAdjoint.star_mul_self x)
  simpa only [he] using h.symm

end Generator.Tracial

end

end OAI
