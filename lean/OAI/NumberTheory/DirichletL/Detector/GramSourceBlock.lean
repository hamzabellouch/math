import OAI.NumberTheory.DirichletL.Detector.GramPhysicalScale
import OAI.NumberTheory.DirichletL.Detector.GramShell
import OAI.NumberTheory.DirichletL.Detector.GramJointProfile

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma jointProfile_physicalPoint (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (v T : ℝ) (hT : 0≤T) (N : ℝ) (hN : 0<N) (m : O×O) :
    ProbeGramJointConstruction.jointProfile W U a b ha hab hs hW v T hT
      (ProbeGramLatticeDecay.physicalPoint N m)=
      shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N) := by
  rw [ProbeGramJointConstruction.jointProfile_apply]
  unfold ProbeGramJointConstruction.rawProfile ProbeGramJointConstruction.q1 ProbeGramJointConstruction.q2
  change lowGramProfile W v _ * star (lowGramProfile W v _) * _ = _
  have h₁ : ‖WithLp.fst (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.1‖^2/N := physicalPoint_first_norm N hN m
  have h₂ : ‖WithLp.snd (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.2‖^2/N := physicalPoint_second_norm N hN m
  rw [h₁,h₂]
  rfl

theorem literal_nonexceptional_source (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(U : SchwartzMap ℝ ℂ)(v T : ℝ),0≤T→∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H₀,K₀,hK₀,hblock⟩ := literal_nonexceptional_block A hA a₀ b₀ ha₀ hab
  obtain ⟨J,H,hprofile⟩ := ProbeGramJointProfile.jointProfile_uniform_degree a₀ b₀ ha₀ hab B H₀
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K₁,hK₁,hprofile⟩ := hprofile W hs hW
  refine ⟨K₀*K₁,mul_pos hK₀ hK₁,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he U v T hT d N hN
  let V := ProbeGramJointConstruction.jointProfile W U a₀ b₀ ha₀ hab hs hW v T hT
  have hv := ProbeGramJointConstruction.jointProfile_annularSupport W U a₀ b₀ ha₀ hab hs hW v T hT
  have hb := hblock S hS σ C k hC hk0 u a b r hr hk P hg c hc hfac p hp0 hgp hchar hfixed hcommon he V hv d N hN
  have hfun : (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
      V (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
    funext m
    rw [jointProfile_physicalPoint W U a₀ b₀ ha₀ hab hs hW v T hT N hN m]
  rw [hfun] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm : 0≤min (1:ℝ) (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
      Ideal.absNorm (Ideal.span {k})/N)^A) := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprofile U v T hT) hK₀.le)
        (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {C})))) (sq_nonneg N)) hm
  convert hh using 1 ; ring

end SevenEighths.ProbeGramCommon
end

end OAI
