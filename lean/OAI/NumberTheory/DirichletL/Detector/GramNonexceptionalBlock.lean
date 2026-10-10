import OAI.NumberTheory.DirichletL.Detector.GramResidue
import OAI.NumberTheory.DirichletL.Detector.GramPeriodicPoisson

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "Joint" => ProbeGramPeriodicPoisson.Joint

theorem literal_nonexceptional_block (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃H : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(W : SchwartzMap Joint ℂ),ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W→
      ∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)‖≤
        K*ProbeGramLatticeDecay.sourceControl H W*(Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H,K,hK,hengine⟩ := ProbeGramPeriodicPoisson.ideal_annular_periodic_bound A hA a₀ b₀ ha₀ hab
  refine ⟨H,K,hK,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he W hW d N hN
  have hcount : (normalizedFactors (Ideal.span {k})).count p=
      (normalizedFactors (Ideal.span {r})).count p := by
    rw [hk]
    exact good_factor_count p hgp hchar u a b r hr
  have heR : ¬6∣(normalizedFactors (Ideal.span {r})).count p := hcount ▸ he
  obtain ⟨M,hM,hMN,hres⟩ := exists_nonexceptional_residue S hS σ C k hC hk0 u a b r hr hk
    P hg c hc hfac p hp0 hgp hchar hfixed hcommon heR
  let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype (O⧸M) := Fintype.ofFinite _
  obtain ⟨f,hf,hfn,hfm⟩ := hres d
  have hmean : (∑'v : (O⧸M)×(O⧸M),f v.1 v.2)=0 := by
    rw [tsum_fintype,Fintype.sum_prod_type]
    exact hfm
  have hh := hengine W hW M hM (fun v=>f v.1 v.2) (Ideal.absNorm (Ideal.span {C}))
    (Nat.cast_nonneg _) (fun v=>hfn v.1 v.2) hmean N hN
  have hfun : (fun m : O×O=>f (ProbeGramPeriodicPoisson.idealQuotientPair M m).1
      (ProbeGramPeriodicPoisson.idealQuotientPair M m).2*W (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) := by
    funext m
    rw [ProbeGramPeriodicPoisson.idealQuotientPair,hf]
  rw [hfun] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold ProbeGramLatticeDecay.sourceControl;positivity)
  apply min_le_min_left
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hN.le
  exact_mod_cast hMN

end SevenEighths.ProbeGramCommon
end

end OAI
