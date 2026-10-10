import Mathlib
import OAI.Probability.SKGap.Matrix.WordDiag
import OAI.Probability.SKGap.Stability.UniformOrdinary
import OAI.Probability.SKGap.Localization.UniformRecipeClass
import OAI.Probability.SKGap.Localization.CoefficientInputBridge

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
universe u
variable {Ω : Type u} {n : Ω→ℕ}

structure FiniteRecipeControl (j : ℝ) (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ)
    (M Nmax : ℕ) (A : ℝ) : Prop where
  small : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (N p : ℕ) (K : ℝ), FamilyRecipe j J h D N p K → N≤Nmax → K≤A →
    ∃C : ℝ,0≤C ∧ ∀a x,SmallBound ((D a).source N) x C ∧
      (∀q,SmallBound ((D a).sourcePartial N q) x C) ∧
      (∑i,|derivativeMatrix ((D a).source N) x i i|)≤C
  means : ∀ {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
    (N p : ℕ) (K : ℝ), FamilyRecipe j J h D N p K → N≤Nmax → K≤A →
    ∀b:Fin N,UniformMultiplier (fun a=>siteMean ((D a).auxCoefficient N b))
  parameter : ∀q:Fin M,UniformMultiplier
    (fun a x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x))

variable {M : ℕ} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

theorem finite_recipe_control (D₀ : ∀a,OrdinaryData (n a) (Fin M) (Fin M) Unit)
    (H₀ : FamilyRecipe j J h D₀ 0 0 1)
    (T : ∀a,Spin (n a)→Fin M→SourceTree (Fin (n a)→ℝ)) (c : LocalConstants)
    (hc : ∀a x,LocalOrdinaryInput (D₀ a) (T a x) x 0 c)
    (Nmax L : ℕ) (A W B Q : ℝ) (hA : 1≤A) (hW : 0≤W) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀a x q,mass ((T a x q).words j).1≤Q ∧ mass ((T a x q).words j).2≤Q)
    (hT : ∀a x q,PolynomialControl A L ((T a x q).words j).1 ∧
      PolynomialControl A L ((T a x q).words j).2)
    (hw : ∀a,WordTestBound (J a) A W (2*Nmax+3))
    (hd : ∀a,WordDiagramBound (J a) j A B (L+2*Nmax+2)) :
    FiniteRecipeControl j J h M Nmax A := by
  have transfer {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) (Fin M) σ)
      (N p : ℕ) (K : ℝ) (H : FamilyRecipe j J h D N p K) (hKA : K≤A) :
      ∃c' : LocalConstants,c'.A=A ∧ ∀a x,LocalOrdinaryInput (D a) (T a x) x N c' := by
    obtain ⟨S,hS,hs⟩:=H.seed
    refine ⟨c.withCoefficient A S hA hS,rfl,fun a x=>?_⟩
    obtain ⟨hJ,hj,hH,hp,hθ⟩:=H.sameEnvironment H₀ a
    exact (hc a x).with_coefficients (D a) hJ hj hH hp hθ N A S hA hS (hs a)
      ((H.coefficients a x).mono hKA)
  constructor
  · intro σ inst D N p K H hN hKA
    obtain ⟨c',hAc,hi⟩:=transfer D N p K H hKA
    apply uniform_ordinary_control D T N L c' j H.coupling hi hW hB hQ hm
    · simpa only [hAc] using hT
    · intro a w hlen hb
      rw [H.interaction a,hAc] at *
      exact hw a w (hlen.trans (by omega)) hb
    · intro a w hlen hb
      rw [H.interaction a,hAc] at *
      exact hd a w (hlen.trans (by omega)) hb
  · intro σ inst D N p K H hN hKA b
    obtain ⟨c',hAc,hi⟩:=transfer D N p K H hKA
    exact uniform_auxiliary_mean D T N c' hi b
  · intro q
    refine ⟨|j|,c.V,abs_nonneg _,c.V_nonneg,
      fun a x=>onsager_parameter_bound j (J a) (h a) q.val x,fun a x=>?_⟩
    have hh : ‖derivativeVector ((D₀ a).θ q) x‖≤c.V :=
      (Finset.single_le_sum (fun r _=>norm_nonneg (derivativeVector ((D₀ a).θ r) x))
        (Finset.mem_univ q)).trans (hc a x).parameter
    have hs:=pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [H₀.parameter a q,EuclideanSpace.real_norm_sq_eq] at hs
    exact hs

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static
variable {n M : ℕ}

def emptyRecipe (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (M : ℕ) :
    OrdinaryData n (Fin M) (Fin M) Unit where
  J:=J
  j:=j
  H:=fun q=>fld j J h q.val
  predecessor:=fun q=>mag j J h q.val
  θ:=fun q x=>j*(onsager j J h (q.val+1) x-onsager j J h q.val x)
  seed:=0
  seedFunction:=fun _ _ _ _=>0
  seedDerivative:=fun _ _ _ _=>0
  auxFunction:=fun _ _ _ _=>0
  auxDerivative:=fun _ _ _ _=>0

lemma emptyRecipe_coefficients (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (M N : ℕ) (x : Spin n) :
    (emptyRecipe j J h M).CoefficientClass N x 1 := by
  refine ⟨le_rfl,?_,?_,?_,?_⟩
  · intro a ha s; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [SegmentValue,emptyRecipe]
  · intros; norm_num [SegmentValue,emptyRecipe]

lemma emptyRecipe_family {Ω : Type*} {n : Ω→ℕ} (j : ℝ)
    (J : ∀a,Interaction (n a)) (h : ∀a,Fin (n a)→ℝ) (M : ℕ) :
    FamilyRecipe j J h (fun a=>emptyRecipe j (J a) (h a) M) 0 0 1 := by
  refine ⟨fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,
    ⟨0,le_rfl,?_⟩,fun a x=>emptyRecipe_coefficients j (J a) (h a) M 0 x,?_⟩
  · intro a; simp [emptyRecipe,vectorNorm]
  · intro a r hr q hq; omega

lemma emptyRecipe_local (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (M : ℕ)
    (T : Fin M→SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)) (x : Spin n)
    {P L E V : ℝ} (hP : 0≤P) (hL : 0≤L) (hE : 0≤E) (hV : 0≤V) (hn : 0<n)
    (hJ : SKGap.opNorm J≤L)
    (hshape : ∀q:Fin M,ShapeBound (derivativeMatrix (fld j J h q.val) x) P)
    (hfield : ∀q:Fin M,‖derivativeMatrix (fld j J h q.val) x-
      SKGap.Noncrossing.Primary.SourceTree.fieldMatrix j J (T q)‖≤E)
    (hsource : ∀q:Fin M,‖derivativeMatrix (mag j J h q.val) x-
      SKGap.Noncrossing.Primary.SourceTree.sourceMatrix j J (T q)‖≤E)
    (hderiv : ∀q:Fin M,SKGap.opNorm (derivativeMatrix (mag j J h q.val) x)≤P)
    (hparam : (∑q:Fin M,‖derivativeVector (fun y=>j*(onsager j J h (q.val+1) y-onsager j J h q.val y)) x‖)≤V) :
    LocalOrdinaryInput (emptyRecipe j J h M) T x 0
      ⟨1,1,P,L,E,V,0,le_rfl,zero_le_one,le_rfl,hP,hL,hE,hV,le_rfl⟩ := by
  refine ⟨hn,hJ,hshape,hfield,hsource,?_,hderiv,?_,hparam,?_,?_,?_,?_⟩
  · intro q i; exact primaryState_mag_bounded j J h q.val x i
  · simp [emptyRecipe,vectorNorm]
  · intro a ha s; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intro a ha b; exact (segmentRegular_const _ _ x 0).mono zero_le_one
  · intros; norm_num [OrdinaryData.seedCoefficient,coefficient,emptyRecipe]
  · intros; norm_num [OrdinaryData.auxCoefficient,coefficient,emptyRecipe]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries MeasureTheory ProbabilityTheory Real Set

theorem primary_uniform_two_seminorms {j : ℝ} (hj : 0<j) (hj1 : j<1)
    (k : ℕ) (hk : 0<k) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀ n,N≤n →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ (p : Bool) (a : ℕ→Fin n→ℝ), (∀ l i,|a l i|≤1) ∧
          C< matrixWordSeminorm p (primaryMatrix j (removeDiagonal (goeMatrix (j/n) g)) a k)} ≤
      2*((wordPatternSet (2*k) (2*k)).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
        ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) +
        (ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
          ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n)))))) := by
  have hs : sqrt j*(1:ℝ)<1 := by
    nlinarith [sq_sqrt hj.le,sqrt_nonneg j]
  obtain ⟨C,N,hC,hN,hgood⟩ := zeroDiag_exact_words_two_seminorms
    hj (by norm_num : (0:ℝ)<1) hs (by norm_num : (1:ℝ)≤1)
    (by norm_num : (1:ℝ)≤1) (by norm_num : (0:ℝ)<1) (2*k)
  refine ⟨massBound j k*C,N,mul_pos (massBound_pos j k) hC,hN,?_⟩
  intro n hn
  have hn0 : 0<n := hN.trans_le hn
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  apply (measure_mono ?_).trans (hgood n hn)
  intro g hg
  obtain ⟨p,a,ha,hlarge⟩ := hg
  by_contra hbad
  have hterm : ∀ t∈primaryPolynomial j a k, matrixWordSeminorm p
      (matrixWord (removeDiagonal (goeMatrix (j/n) g)) t.2-
        Matrix.diagonal (Diagram.prediction j t.2))≤C := by
    intro t ht
    have htB := primaryPolynomial_admissible j a ha k t ht
    apply le_of_not_gt
    intro hlt
    apply hbad
    refine ⟨p,(fun _=>0),liftWord t.2,?_,?_,htB.2,?_,?_,?_⟩
    · intro i; norm_num
    · simpa [liftWord] using htB.1
    · simp
    · exact Or.inl (inverseCount_lift t.2)
    · have he : wordPrediction j (fun _ : Fin n=>0) 1 (liftWord t.2)=Diagram.prediction j t.2 :=
        funext (wordPrediction_lift j _ _ _)
      simpa only [exactWord_lift,he] using hlt
  have hb := primaryMatrix_seminorm p j (removeDiagonal (goeMatrix (j/n) g)) a k hk hterm
  have hm := mul_le_mul_of_nonneg_right (primaryMass_bound j a ha k) hC.le
  exact (not_lt_of_ge (hb.trans hm)) hlarge

end SKGap.Noncrossing.Primary

end
end

end OAI
