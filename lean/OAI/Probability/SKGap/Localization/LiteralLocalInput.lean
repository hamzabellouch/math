import Mathlib
import OAI.Probability.SKGap.Stability.ClosedOrdinaryBridge
import OAI.Probability.SKGap.Localization.FiniteStartedControlGeneral

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein SKGap.Noncrossing.Primary
variable {n M : ℕ}

def literalEnvironmentConstants (j K B A Va Vc : ℝ) (M : ℕ)
    (hK : 0≤K) (hB : 0≤B) (hA : 1≤A) (hVa : 0≤Va) (hVc : 0≤Vc) : LocalConstants :=
  let P:=localPrimaryBudget j K B M
  ⟨A,A,P,K,P,(M:ℝ)*(|j| *(P+P))+Vc+Va,2,hA,by linarith,le_rfl,
    localPrimaryBudget_nonneg hK hB M,hK,localPrimaryBudget_nonneg hK hB M,
    by positivity [localPrimaryBudget_nonneg (j:=j) hK hB M],by norm_num⟩

theorem literal_full_local_input (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (N : ℕ) (hn : 0<n) (he : vectorNorm e≤1)
    {K B A Va Vc : ℝ} (hK : 0≤K) (hB : 0≤B) (hA : 1≤A) (hVa : 0≤Va) (hVc : 0≤Vc)
    (hop : SKGap.opNorm J≤K) (hformal : ∀q<M,ShapeBound (formalField j J h x q) B)
    (ha : ‖derivativeVector a x‖≤Va) (hc : ‖derivativeVector (fun v=>Real.sqrt (n:ℝ)*c v) x‖≤Vc)
    (hcoeff : (literalFullData j J h l f a c r e).CoefficientClass N x A) :
    LocalOrdinaryInput (literalFullData j J h l f a c r e)
      (fun q=>primaryTree j J h x q.val) x N
      (literalEnvironmentConstants j K B A Va Vc M hK hB hA hVa hVc) := by
  have hp:=primary_local_input J h x hn hK hB hop M hformal
  refine ⟨hn,hop,hp.primaryShape,hp.primaryFieldError,hp.primarySourceError,
    hp.primaryValue,hp.primaryDerivative,?_,?_,hcoeff.seedRegular,hcoeff.auxRegular,?_,?_⟩
  · exact literalInitial_seed_bound J j f (fld j J h l.val) (mag j J h l.val) a c r e hn he
  · change (∑q : Fin M⊕Bool,‖derivativeVector (literalFullParameters j J h a c q) x‖)≤_
    rw [Fintype.sum_sum_type,Fintype.sum_bool]
    have hh:=hp.parameter
    change (∑q : Fin M,‖derivativeVector (fun v=>j*(onsager j J h (q.val+1) v-onsager j J h q.val v)) x‖)≤_ at hh
    change (∑q : Fin M,‖derivativeVector (fun v=>j*(onsager j J h (q.val+1) v-onsager j J h q.val v)) x‖)+
      (‖derivativeVector (fun v=>Real.sqrt (n:ℝ)*c v) x‖+‖derivativeVector a x‖)≤_
    dsimp only [literalEnvironmentConstants]
    linarith
  · intro b hb s i;exact (hcoeff.seedValue b hb s).at i
  · intro b hb s i;exact (hcoeff.auxValue b hb s).at i

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}

theorem literal_finite_control (j : ℝ) (J : ∀b,Interaction (n b))
    (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
    (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
    (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
    (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
    {K B R Bc Va Vc A V S F W C : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hBc : 0≤Bc) (hVa : 0≤Va) (hVc : 0≤Vc)
    (hA : 1≤A) (hV : 0≤V) (hS : 0≤S) (hF : 0≤F) (hW : 0≤W) (hC : 0≤C)
    (hop : ∀b,SKGap.opNorm (J b)≤K)
    (hformal : ∀b x,∀q<M,ShapeBound (formalField j (J b) (h b) x q) B)
    (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
    (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤Bc)
    (hDa : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (a b) x‖≤Va)
    (hDc : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (fun v=>Real.sqrt (n b:ℝ)*c b v) x‖≤Vc)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x)
    (hdiag : ∀b x,x∈flipNeighborhood (E b)→LiteralInitialDiagnostics
      (literalInitial (J b) j (Real.sqrt (n b:ℝ)) f (fld j (J b) (h b) l.val)
        (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b))
      (w b) (y b) (primaryTree j (J b) (h b) x l.val) x V S F A)
    (Nmax : ℕ)
    (hw : ∀b x,x∈flipNeighborhood (E b)→ClosedWordTestBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A W (2*Nmax+5))
    (hd : ∀b x,x∈flipNeighborhood (E b)→ClosedWordDiagramBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) A C (2*M+2*Nmax+4)) :
    FiniteLocalRecipeControl E j J h (fun b=>literalFullParameters (M:=M) j (J b) (h b) (a b) (c b))
      w y M Nmax A := by
  let D:=fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)
  let I:=fun b=>literalInitial (J b) j (Real.sqrt (n b:ℝ)) f (fld j (J b) (h b) l.val)
    (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b)
  let K₀:=literalCoefficientBudget f j R Bc
  have hK₀ : 1≤K₀ := by
    have h2 : 0≤f.mass*Real.exp (R/2):=mul_nonneg f.mass_nonneg (Real.exp_pos _).le
    have h3 : 0≤(1+|j| *|Bc|)*phiExpr.mass*Real.exp (R/2):=by positivity [phiExpr.mass_nonneg]
    dsimp [K₀,literalCoefficientBudget];linarith [abs_nonneg (initialRegularBudget f j R Bc)]
  have H:=literal_full_local_family j J h l f a c r e w y E hn he hBc ha hc heq
  have H₀:=H.mono (Nat.zero_le l.val) le_rfl le_rfl (le_refl K₀)
  have hi : ∀b x,x∈flipNeighborhood (E b)→LocalOrdinaryInput (D b)
      (fun q=>primaryTree j (J b) (h b) x q.val) x 1
      (literalEnvironmentConstants j K B K₀ Va Vc M hK hB hK₀ hVa hVc) := by
    intro b x hx
    exact literal_full_local_input j (J b) (h b) l f (a b) (c b) (r b) (e b) x 1
      (hn b) (he b) hK hB hK₀ hVa hVc (hop b) (hformal b x) (hDa b x hx) (hDc b x hx)
      (H.coefficients b x hx)
  have hm (b : Ω) (x : Spin (n b)) (q : Fin M) :
      Marked.mass (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).1≤(2+|j|)^M ∧
      Marked.mass (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).2≤(2+|j|)^M := by
    have hb:=ordinary_mass_bridge j (primaryTree j (J b) (h b) x q.val)
    rw [hb.1,hb.2]
    have hm:=primaryTree_mass (hn b) j (J b) (h b) x q.val
    have hp : (2+|j|)^q.val≤(2+|j|)^M:=pow_le_pow_right₀ (by linarith [abs_nonneg j]) q.isLt.le
    exact ⟨hm.1.trans hp,hm.2.trans hp⟩
  have ht (b : Ω) (x : Spin (n b)) (q : Fin M) :
      GradedControl A (2*M+1) (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).1 ∧
      GradedControl A (2*M+1) (GradedWords.ordinaryWords j (primaryTree j (J b) (h b) x q.val)).2 := by
    apply ordinary_control_bridge
    have hv:=primaryTree_control j (J b) (h b) x q.val hA
    exact ⟨hv.1.mono (by omega),hv.2.mono (by omega)⟩
  apply finite_started_control_seeds D K₀ H₀ I (fun _=>rfl) (fun _=>rfl)
    (fun b x q=>primaryTree j (J b) (h b) x q.val) (fun b x=>primaryTree j (J b) (h b) x l.val)
    (literalEnvironmentConstants j K B K₀ Va Vc M hK hB hK₀ hVa hVc) A hi Sum.inl
    (fun _ _=>rfl) Nmax (2*M+1) S F V W C ((2+|j|)^M) hA hS hF hV hW hC (by positivity)
  · exact fun b x hx=>(hdiag b x hx).source
  · exact fun b x hx=>(hdiag b x hx).source_flip
  · exact fun b x hx=>(hdiag b x hx).field
  · exact fun b x hx=>(hdiag b x hx).field_flip
  · exact fun b x hx=>(hdiag b x hx).coefficient_nonneg
  · exact fun b x hx=>(hdiag b x hx).inverse_pos
  · exact fun b x hx=>(hdiag b x hx).source_bound
  · exact fun b x hx=>(hdiag b x hx).field_bound
  · exact fun b x hx=>(hdiag b x hx).partial_bound.size
  · exact fun b x hx=>(hdiag b x hx).source_trace
  · exact fun b x hx=>(hdiag b x hx).field_trace
  · exact fun b x hx=>(hdiag b x hx).coefficient_bound
  · exact fun b x _ q=>hm b x q
  · exact fun b x _=>hm b x l
  · exact fun b x _ q=>ht b x q
  · exact fun b x _=>ht b x l
  · intro b x hx
    have hcoef : (I b).implicitCoefficient x=fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x) :=
      funext fun i=>literalInitial_coefficient _ _ _ _ _ _ _ _ _ _ _ _
    rw [hcoef];exact hw b x hx
  · intro b x hx
    have hcoef : (I b).implicitCoefficient x=fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x) :=
      funext fun i=>literalInitial_coefficient _ _ _ _ _ _ _ _ _ _ _ _
    rw [hcoef]
    convert hd b x hx using 1
    omega

end SKGapCutoff.Recipe

end
end

end OAI
