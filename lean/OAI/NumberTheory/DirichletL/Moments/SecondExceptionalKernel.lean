import OAI.NumberTheory.DirichletL.Moments.ExceptionalKernel
import OAI.NumberTheory.DirichletL.Moments.SecondIdealBlockBound

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalKernel
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentMobiusRegroup CenteredMomentFixedRay CenteredMomentRowNorm
open CenteredMomentSmooth CenteredMomentCauchy CenteredMomentPlainChildEnergy
open CenteredMomentSecondScaled CenteredMomentExceptionalKernel RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem whole_kernel_divisor_pair (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ)
    (M : Fin 4→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0→|y|≤M i) (A J : ℕ) :
    ∃C:ℝ,0≤C ∧ ∀R:ℝ,0<R →
      ∀{α β:Type*}(Ls:Finset (Ideal O))(rows:Finset O)(S:Finset α)(T:Finset β)
        (a:α→O)(b:β→O)(c:Ideal O→α→ℂ)(d:Ideal O→β→ℂ)
        (u:α→ℝ)(v:β→ℝ)(ρ x:O→ℝ)(η:O→ℂ),
      (∀z∈rows,‖η z‖≤1) → (∀z∈rows,‖V 0 (ρ z)‖≤1) →
      (∀z∈rows,‖V 1 (x z)‖≤1) → ∀E:ℝ,0≤E →
      (∀t:ℝ,(∑L∈Ls,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
        ∑z∈rows,‖rowPolynomial S a (fun i=>c L i*columnPhase (V 2) (u i) t) z‖*
          ‖rowPolynomial T b (fun j=>d L j*star (columnPhase (V 3) (v j) t)) (-z)‖)
        ≤E*(1+‖t‖)^J) →
      (1+R)^A*‖∑L∈Ls,(UniqueFactorizationMonoid.moebius L:ℂ)*
        ∑z∈rows,η z*∑i∈S,∑j∈T,
          ((c L i*idealRowHom z (Ideal.span {a i}))*
            star (d L j*idealRowHom (-z) (Ideal.span {b j})))*
              wholeKernel W V R (ρ z) (x z) (u i) (v j)‖≤C*E := by
  obtain ⟨C,hC,hbound⟩:=whole_kernel_paired_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro R hR α β Ls rows S T a b c d u v ρ x η hη hV₀ hV₁ E hE he
  have hh:=hbound R hR (Ls×ˢrows) S T
    (fun k i=>(UniqueFactorizationMonoid.moebius k.1:ℂ)*(c k.1 i*idealRowHom k.2 (Ideal.span {a i})))
    (fun k j=>d k.1 j*idealRowHom (-k.2) (Ideal.span {b j})) u v
    (fun k=>ρ k.2) (fun k=>x k.2) (fun k=>η k.2)
    (fun k hk=>hη k.2 (Finset.mem_product.mp hk).2)
    (fun k hk=>hV₀ k.2 (Finset.mem_product.mp hk).2)
    (fun k hk=>hV₁ k.2 (Finset.mem_product.mp hk).2) E hE
  have hl (L:Ideal O)(z:O)(t:ℝ):
      leftColumn S (fun i=>(UniqueFactorizationMonoid.moebius L:ℂ)*(c L i*idealRowHom z (Ideal.span {a i})))
        (V 2) u t=(UniqueFactorizationMonoid.moebius L:ℂ)*
          rowPolynomial S a (fun i=>c L i*columnPhase (V 2) (u i) t) z := by
    rw [←leftColumn_eq_rowPolynomial]
    unfold leftColumn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp:∀t:ℝ,(∑k∈Ls×ˢrows,
      ‖leftColumn S (fun i=>(UniqueFactorizationMonoid.moebius k.1:ℂ)*(c k.1 i*idealRowHom k.2 (Ideal.span {a i}))) (V 2) u t‖*
      ‖rightColumn T (fun j=>d k.1 j*idealRowHom (-k.2) (Ideal.span {b j})) (V 3) v t‖)
      ≤E*(1+‖t‖)^J:=by
    intro t
    simp only [Finset.sum_product,hl,rightColumn_eq_star_rowPolynomial,norm_star,norm_mul,mul_assoc,←Finset.mul_sum]
    exact he t
  have hout:=hh hp
  apply hout.trans_eq'
  congr 2
  simp only [Finset.sum_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem weighted_norm_sum {α:Type*} (S:Finset α)(a f:α→ℂ)
    (r:ℝ)(hr:0≤r)(B:α→ℝ)(hB:∀i∈S,r*‖f i‖≤B i):
    r*‖∑i∈S,a i*f i‖≤∑i∈S,‖a i‖*B i:=by
  calc
    _≤r*∑i∈S,‖a i*f i‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _=∑i∈S,‖a i‖*(r*‖f i‖):=by simp only [Finset.mul_sum,norm_mul];congr 1;funext i;ring
    _≤_:=Finset.sum_le_sum (fun i hi=>mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem whole_kernel_actual_second_pair (W : 𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (M:Fin 4→ℝ)(hM:∀i,0≤M i)(hV:∀i y,V i y≠0→|y|≤M i)(A J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀R:ℝ,0<R →
      ∀{α β:Type*}(rows:Finset O)(S:Finset α)(T:Finset β)
        (D E A₀:O)(a:α→O)(b:β→O)
        (hD:Supported (Ideal.span {D}))(hE:Supported (Ideal.span {E}))
        (ha:∀i,Supported (Ideal.span {a i}))(hb:∀j,Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2∣D-1) →
      (ConcretePrimeRowBridge.goodLambda^2∣E-1) →
      (∀i,ConcretePrimeRowBridge.goodLambda^2∣a i-1) →
      (∀j,ConcretePrimeRowBridge.goodLambda^2∣b j-1) →
      (∀i,IsCoprime (D*E) (a i)) → (∀j,IsCoprime (D*E) (b j)) →
      ∀(q:O→ℂ)(c:α→ℂ)(d:β→ℂ)(u:α→ℝ)(v:β→ℝ)(ρ x:O→ℝ),
      (∀z∈rows,‖q z*actualCorrelation D E hD hE (A₀*z)‖≤1) →
      (∀z∈rows,‖V 0 (ρ z)‖≤1) → (∀z∈rows,‖V 1 (x z)‖≤1) →
      ∀E0:ℝ,0≤E0 →
      (∀χ ξ:RayCharacter,∀t:ℝ,
        (∑L∈divisorPool T (fun j=>Ideal.span {b j}),‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
          ∑z∈rows,
            ‖rowPolynomial S a (fun i=>divisorCoefficient L a (movingCoefficient A₀ a c) χ i*
              columnPhase (V 2) (u i) t) z‖*
            ‖rowPolynomial T b (fun j=>divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*
              star (columnPhase (V 3) (v j) t)) (-z)‖)≤E0*(1+‖t‖)^J) →
      (1+R)^A*‖∑z∈rows,q z*∑i∈S,∑j∈T,
        (if IsCoprime (a i) (b j) then actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0)*(c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖≤C*E0:=by
  obtain ⟨C,hC,hbound⟩:=whole_kernel_divisor_pair W V M hM hV A J
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ E0 hE0 hpair
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  let f:RayCharacter→RayCharacter→ℂ:=fun χ ξ=>
    ∑L∈divisorPool T (fun j=>Ideal.span {b j}),(UniqueFactorizationMonoid.moebius L:ℂ)*
      ∑z∈rows,(q z*actualCorrelation D E hD hE (A₀*z))*∑i∈S,∑j∈T,
        ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i}))*
          star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j})))*
            wholeKernel W V R (ρ z) (x z) (u i) (v j)
  have hf:∀χ ξ,(1+R)^A*‖f χ ξ‖≤C*E0:=by
    intro χ ξ
    exact hbound R hR _ rows S T a b
      (fun L=>divisorCoefficient L a (movingCoefficient A₀ a c) χ)
      (fun L=>divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹))
      u v ρ x (fun z=>q z*actualCorrelation D E hD hE (A₀*z)) hq hV₀ hV₁ E0 hE0 (hpair χ ξ)
  have heq:(∑L∈divisorPool T (fun j=>Ideal.span {b j}),
      (UniqueFactorizationMonoid.moebius L:ℂ)*∑χ:RayCharacter,∑ξ:RayCharacter,
        pairCoeff (phaseTable D E) χ ξ *
          ∑z∈rows,(q z*actualCorrelation D E hD hE (A₀*z))*∑i∈S,∑j∈T,
            ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i}))*
              star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j})))*
                wholeKernel W V R (ρ z) (x z) (u i) (v j))=
        ∑χ:RayCharacter,∑ξ:RayCharacter,pairCoeff (phaseTable D E) χ ξ*f χ ξ:=by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ξ hξ
    unfold f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  calc
    _≤∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖*(C*E0):=by
      have hh:=weighted_norm_sum Finset.univ (fun _:RayCharacter=>(1:ℂ))
        (fun χ=>∑ξ:RayCharacter,pairCoeff (phaseTable D E) χ ξ*f χ ξ) ((1+R)^A) (by positivity)
        (fun χ=>∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖*(C*E0))
        (fun χ _=>weighted_norm_sum Finset.univ _ _ ((1+R)^A) (by positivity) _ (fun ξ _=>hf χ ξ))
      simpa only [one_mul,norm_one] using hh
    _=(∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff (phaseTable D E) χ ξ‖)*(C*E0):=by
      simp only [Finset.sum_mul]
    _≤256*(C*E0):=mul_le_mul_of_nonneg_right (phaseTable_mass D E) (mul_nonneg hC hE0)
    _=(256*C)*E0:=by ring

open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSupport CenteredMomentRestrictedEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredExceptionalProfile

theorem exceptional_rows_pair (η:Character)(χ₀ χ ξ:RayCharacter)(Q:Ideal O)
    (hQ:Q≤Ideal.span {(72:O)})(m A:O)(hmLam:ConcretePrimeRowBridge.goodLambda∣m)
    (hm2:(2:O)∣m)(rows:Finset O)
    (hrows:∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z):
    (∀z∈rows,FixedInducingRow (childCharacter η χ) Q m A z) ∧
    (∀z∈rows,FixedInducingRow (childCharacter η (ξ⁻¹)) Q m A (-z)):=by
  constructor
  · intro z hz
    have hh:=CenteredMomentExceptionalReflection.fixedInducingRow_reflected
      η χ₀ χ₀ Q hQ m A z hmLam hm2 (hrows z hz)
    simpa only [neg_neg] using
      CenteredMomentExceptionalReflection.fixedInducingRow_reflected
        η χ₀ χ Q hQ m A (-z) hmLam hm2 hh
  · intro z hz
    exact CenteredMomentExceptionalReflection.fixedInducingRow_reflected
      η χ₀ (ξ⁻¹) Q hQ m A z hmLam hm2 (hrows z hz)

theorem actual_exceptional_block_bound (W:𝓢(ℝ,ℂ))(decay J:ℕ):
    ∃B:ℝ,0≤B ∧ ∀r:ℝ,0<r →
      ∀(η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
        (C D:Ideal O)(hC:Supported C)(hD:Supported D),
      primeSupport C=primeSupport D →
      ∀(U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)
        (ρ x:O→ℝ)(u:sectorPool C hC.1 S→ℝ)(v:sectorPool D hD.1 S→ℝ)
        (Q:Ideal O)(m:O)(χ₀:RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c:=fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d:=fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I
      (∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z) →
      ∀E:ℝ,0≤E →
      (∀χ ξ:RayCharacter,
        (∀z∈rows,FixedInducingRow (childCharacter η χ) Q m A z) →
        (∀z∈rows,FixedInducingRow (childCharacter η (ξ⁻¹)) Q m A (-z)) →
        ∀w:ℝ,
        (∑L∈divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
          ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
            (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
              (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) z‖*
          ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
            (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
              (movingCoefficient A (sectorElement D hD.1 S) d) (ξ⁻¹) I*star (columnPhase logAnnulus (v I) w)) (-z)‖)
          ≤E*(1+‖w‖)^J) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤B*E:=by
  obtain ⟨B,hB,hbound⟩:=whole_kernel_actual_second_pair W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ x hx=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure x hx) decay J
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v Q m χ₀ hQ hmLam hm2
  dsimp only
  intro hrows E hE hpair
  have hcopD (I:sectorPool D hD.1 S):
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S I):=by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S I
  have he:=hbound r hr rows Finset.univ Finset.univ (primaryGenerator C) (primaryGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun I=>β (D*I)*heightCoeff η t I) u v ρ x
    (fun z _=>actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _) E hE
  have hh:∀χ ξ:RayCharacter,∀w:ℝ,
      (∑L∈divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
        ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
          (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
              (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*columnPhase logAnnulus (u I) w) z‖*
        ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
          (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
              (sectorElement D hD.1 S) (fun I=>β (D*I)*heightCoeff η t I)) (ξ⁻¹) I*
              star (columnPhase logAnnulus (v I) w)) (-z)‖)≤E*(1+‖w‖)^J:=by
    intro χ ξ w
    have hg:=exceptional_rows_pair η χ₀ χ ξ Q hQ m _ hmLam hm2 rows hrows
    exact hpair χ ξ hg.1 hg.2 w
  have he':=he (by simpa only [sectorElement_span] using hh)
  have hcop (I:sectorPool C hC.1 S)(J:sectorPool D hD.1 S):
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  have hcop' (I:sectorPool C hC.1 S)(J:sectorPool D hD.1 S):
      IsCoprime (primaryGenerator (I:Ideal O)) (primaryGenerator (J:Ideal O)) ↔
        IsCoprime (I:Ideal O) (J:Ideal O):=hcop I J
  simpa only [sectorElement_span,idealCorrelation,primaryGenerator_mul,sectorElement,hcop'] using he'

end SevenEighths.CenteredMomentSecondExceptionalKernel

end

end OAI
