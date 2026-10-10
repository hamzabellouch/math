import OAI.Geometry.Relativity.CKS.PhysicalCurvatureOperator

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationMetric_contDiffAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => foliationMetric (U y) (γ y) (s y)) x := by
  have hγc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hrr : ContDiffAt ℝ ∞
      (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x :=
    (contDiffAt_const.div (hU.pow 2) (pow_ne_zero _ h0)).add
      (ContDiffAt.sum (fun a _ => ContDiffAt.sum
        (fun b _ => ((hγc a b).mul (hsc a)).mul (hsc b))))
  have hm (a) : ContDiffAt ℝ ∞ (fun y => ∑ b, γ y a b*s y b) x :=
    ContDiffAt.sum (fun b _ => (hγc a b).mul (hsc b))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hm 0
  · exact hm 1
  · exact hm 0
  · exact hγc 0 0
  · exact hγc 0 1
  · exact hm 1
  · exact hγc 1 0
  · exact hγc 1 1

lemma adaptedFrame_contDiffAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hp : (γ x).PosDef) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have hγc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have h00 : 0 < γ x 0 0 := hp.diag_pos
  have ha := (hγc 0 0).sqrt h00.ne'
  have hd : ContDiffAt ℝ ∞ (fun y => (γ y).det) x := by
    simpa only [Matrix.det_fin_two] using
      ((hγc 0 0).mul (hγc 1 1)).sub ((hγc 0 1).mul (hγc 1 0))
  have hb := hd.sqrt hp.det_pos.ne'
  have hapos := Real.sqrt_pos.mpr h00
  have hbpos := Real.sqrt_pos.mpr hp.det_pos
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hU
  · exact hU.neg.mul (hsc 0)
  · exact hU.neg.mul (hsc 1)
  · exact contDiffAt_const
  · exact ha.inv hapos.ne'
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact (hγc 0 1).neg.div (ha.mul hb) (mul_ne_zero hapos.ne' hbpos.ne')
  · exact ha.div hb hbpos.ne'

theorem foliation_scalar_curvature_trace {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    actualFrameScalar G E x =
      ∑ i, ∑ j, metricPair (G x) (curvatureVector G E x i j j) (E i x) := by
  dsimp only
  have ha := (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds
  exact actualScalar_curvature_trace (foliationMetric_contDiffAt hU hγ hs h0)
    (adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds) ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev CovectorJet := I → ScalarJet
abbrev CovariantTensorJet := I → I → ScalarJet

def covectorDiv (q : Jet) (E : CovectorJet) : ℝ :=
  ∑ i, ∑ k, inverse q.1 i k*((E k).2.1 i-∑ a, christoffel q a i k*(E a).1)
def tensorDiv (q : Jet) (T : CovariantTensorJet) (a : I) : ℝ :=
  ∑ i, ∑ k, inverse q.1 i k*((T k a).2.1 i-
    ∑ b, (christoffel q b i k*(T b a).1+christoffel q b i a*(T k b).1))
def covectorLie (S E : CovectorJet) (a : I) : ℝ :=
  ∑ b, ((S b).1*(E a).2.1 b+(E b).1*(S b).2.1 a)
def covectorPair (q : Jet) (E B : I → ℝ) : ℝ :=
  ∑ i, ∑ k, inverse q.1 i k*E i*B k
def tensorPair (q : Jet) (X T : Mat) : ℝ :=
  ∑ i, ∑ k, ∑ a, ∑ b, inverse q.1 i a*inverse q.1 k b*X i k*T a b

def normalMomentum (q : Jet) (H L t Np : ℝ) (X T : Mat)
    (E : CovectorJet) (B : I → ℝ) : ℝ :=
  H*(L-t)-tensorPair q X T-Np+covectorDiv q E-2*covectorPair q (fun a => (E a).1) B

def angularMomentum (q : Jet) (H U : ℝ) (L t : ScalarJet)
    (S E : CovectorJet) (T : CovariantTensorJet) (Er B : I → ℝ) (a : I) : ℝ :=
  U*(Er a-covectorLie S E a)+H*(E a).1+tensorDiv q T a-
    (L.2.1 a+t.2.1 a)+(L.1-t.1)*B a-
      ∑ i, ∑ k, (T i a).1*inverse q.1 i k*B k

abbrev MomentumInput := ℝ × ℝ × Jet × (Fin 5 → ScalarJet) × CovectorJet ×
  CovectorJet × CovariantTensorJet × Mat × (I → ℝ)

abbrev mz (p : MomentumInput) := p.1
abbrev mw (p : MomentumInput) := p.2.1
abbrev mq (p : MomentumInput) := p.2.2.1
abbrev mc (p : MomentumInput) := p.2.2.2.1
abbrev mS (p : MomentumInput) := p.2.2.2.2.1
abbrev mE (p : MomentumInput) := p.2.2.2.2.2.1
abbrev mT (p : MomentumInput) := p.2.2.2.2.2.2.1
abbrev mX (p : MomentumInput) := p.2.2.2.2.2.2.2.1
abbrev mEr (p : MomentumInput) := p.2.2.2.2.2.2.2.2

def normalizedSpeed (p : MomentumInput) : ℝ :=
  Real.sqrt (1+mz p^2)*(1+mz p^3*(mc p 0).1)
def normalizedMean (p : MomentumInput) : ℝ :=
  2*normalizedSpeed p*(1+mz p^3*(mc p 4).1)
def accelerationCoefficient (p : MomentumInput) (a : I) : ℝ :=
  (mc p 0).2.1 a/(1+mz p^3*(mc p 0).1)

def normalResidual (p : MomentumInput) : ℝ :=
  normalizedMean p*((mc p 2).1-(mc p 1).1)-
  mz p^3*tensorPair (mq p) (mX p) (fun i k => (mT p i k).1)-
  2*normalizedSpeed p*((mc p 3).1-mz p^4*∑ a, (mS p a).1*(mc p 1).2.1 a)+
  mz p*covectorDiv (mq p) (mE p)-
  2*mz p^4*covectorPair (mq p) (fun a => (mE p a).1) (accelerationCoefficient p)

def angularResidual (p : MomentumInput) (a : I) : ℝ :=
  normalizedSpeed p*(mEr p a-mz p^4*covectorLie (mS p) (mE p) a)+
  normalizedMean p*(mE p a).1+
  mz p*(tensorDiv (mq p) (mT p) a-(mc p 2).2.1 a-(mc p 1).2.1 a)+
  mw p*mz p^3*accelerationCoefficient p a+
  mz p^4*(((mc p 2).1-(mc p 1).1)*accelerationCoefficient p a-
    ∑ i, ∑ k, (mT p i a).1*inverse (mq p).1 i k*accelerationCoefficient p k)

def momentumResidual (p : MomentumInput) : ℝ × (I → ℝ) :=
  (normalResidual p,angularResidual p)
def momentumRegion : Set MomentumInput :=
  {p | determinant (mq p).1 ≠ 0 ∧ 1+mz p^3*(mc p 0).1 ≠ 0}

lemma momentumRegion_open : IsOpen momentumRegion := by
  apply IsOpen.inter
  · exact isOpen_ne_fun (determinant_smooth.continuous.comp (by fun_prop)) continuous_const
  · exact isOpen_ne_fun (by fun_prop) continuous_const

lemma momentInverse_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (i k : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => inverse (mq p).1 i k) p := by
  have hh := inverse_component_smooth (j := ((mq p),(1,0,0))) ⟨hp.1,by norm_num⟩ i k
  exact hh.comp p (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => ((mq p,(1,0,0)) : CombinedJet)) p)
lemma momentChristoffel_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (a i k : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => christoffel (mq p) a i k) p := by
  exact (christoffel_smooth (j := ((mq p),(1,0,0))) ⟨hp.1,by norm_num⟩ a i k).comp p
    (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => ((mq p,(1,0,0)) : CombinedJet)) p)
lemma normalizedSpeed_smooth : ContDiff ℝ ∞ normalizedSpeed := by
  unfold normalizedSpeed
  exact ((by fun_prop : ContDiff ℝ ∞ (fun p : MomentumInput => 1+mz p^2)).sqrt
    (by intro p; positivity)).mul (by fun_prop)
lemma normalizedMean_smooth : ContDiff ℝ ∞ normalizedMean :=
  (contDiff_const.mul normalizedSpeed_smooth).mul (by fun_prop)
lemma accelerationCoefficient_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (a : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => accelerationCoefficient p a) p :=
  (by fun_prop : ContDiffAt ℝ ∞ (fun p : MomentumInput => (mc p 0).2.1 a) p).div
    (by fun_prop) hp.2
lemma momentCovectorDiv_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => covectorDiv (mq p) (mE p)) p := by
  unfold covectorDiv
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply (momentInverse_smooth hp i k).mul
  apply ContDiffAt.sub (by fun_prop)
  apply ContDiffAt.sum; intro a _
  exact (momentChristoffel_smooth hp a i k).mul (by fun_prop)
lemma momentTensorDiv_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) (a : I) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => tensorDiv (mq p) (mT p) a) p := by
  unfold tensorDiv
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply (momentInverse_smooth hp i k).mul
  apply ContDiffAt.sub (by fun_prop)
  apply ContDiffAt.sum; intro b _
  exact ((momentChristoffel_smooth hp b i k).mul (by fun_prop)).add
    ((momentChristoffel_smooth hp b i a).mul (by fun_prop))
lemma momentTensorPair_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => tensorPair (mq p) (mX p) (fun i k => (mT p i k).1)) p := by
  unfold tensorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  apply ContDiffAt.sum; intro a _
  apply ContDiffAt.sum; intro b _
  exact (((momentInverse_smooth hp i a).mul (momentInverse_smooth hp k b)).mul (by fun_prop)).mul (by fun_prop)
lemma momentCovectorPair_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ (fun p : MomentumInput => covectorPair (mq p) (fun a => (mE p a).1) (accelerationCoefficient p)) p := by
  unfold covectorPair
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  exact ((momentInverse_smooth hp i k).mul (by fun_prop)).mul (accelerationCoefficient_smooth hp k)

lemma momentumResidual_smooth {p : MomentumInput} (hp : p ∈ momentumRegion) :
    ContDiffAt ℝ ∞ momentumResidual p := by
  have hl (a : I) : ContDiff ℝ ∞ (fun p : MomentumInput => covectorLie (mS p) (mE p) a) := by
    unfold covectorLie
    fun_prop
  have hm := normalizedMean_smooth.contDiffAt (x := p)
  have hu := normalizedSpeed_smooth.contDiffAt (x := p)
  apply ContDiffAt.prodMk
  · unfold normalResidual
    apply ContDiffAt.sub
    · apply ContDiffAt.add
      · apply ContDiffAt.sub
        · apply ContDiffAt.sub
          · exact hm.mul (by fun_prop)
          · exact ContDiffAt.mul (by fun_prop) (momentTensorPair_smooth hp)
        · exact (contDiffAt_const.mul hu).mul (by fun_prop)
      · exact ContDiffAt.mul (by fun_prop) (momentCovectorDiv_smooth hp)
    · exact ContDiffAt.mul (by fun_prop) (momentCovectorPair_smooth hp)
  · apply contDiffAt_pi.mpr
    intro a
    unfold angularResidual
    have ht : ContDiffAt ℝ ∞ (fun p : MomentumInput =>
        ∑ i, ∑ k, (mT p i a).1*inverse (mq p).1 i k*accelerationCoefficient p k) p := by
      apply ContDiffAt.sum; intro i _
      apply ContDiffAt.sum; intro k _
      exact (ContDiffAt.mul (by fun_prop) (momentInverse_smooth hp i k)).mul
        (accelerationCoefficient_smooth hp k)
    apply ContDiffAt.add
    · apply ContDiffAt.add
      · apply ContDiffAt.add
        · apply ContDiffAt.add
          · apply hu.mul
            apply ContDiffAt.sub (by fun_prop)
            exact ContDiffAt.mul (by fun_prop) (hl a).contDiffAt
          · exact hm.mul (by fun_prop)
        · exact ContDiffAt.mul (by fun_prop)
            (((momentTensorDiv_smooth hp a).sub (by fun_prop)).sub (by fun_prop))
      · exact ContDiffAt.mul (by fun_prop) (accelerationCoefficient_smooth hp a)
    · apply ContDiffAt.mul (by fun_prop)
      exact (ContDiffAt.mul (by fun_prop) (accelerationCoefficient_smooth hp a)).sub ht

end
end CKSAngularGeometry

end

end OAI
