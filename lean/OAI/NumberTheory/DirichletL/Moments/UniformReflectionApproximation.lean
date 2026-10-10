import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentRetainedReflection CenteredMomentOriginalReflectionApproximation
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem discarded_bound (A B : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y R : ℝ),
      0<Y → 0<R →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨H,D,hD,hDb⟩ := paperRadialFourier_euler_source_weighted_bound (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨H,K*D,mul_pos hK hD,?_⟩
  intro G χ Y R hY hR
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖paperRadialFourier G x‖≤
      D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := by
    intro x hx
    have hh := hDb G 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)
    R (by positivity) hR hf
  exact (hKb χ _ ((D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)/R^A)
    Y (by positivity) hY hm).trans_eq (by ring)

theorem discarded_negligible (xi saving L Cscale : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨H,C,hC,hbound⟩ := discarded_bound A 2 (by omega)
  refine ⟨H,C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro G χ Y Z hZ hY hYZ
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A :=
      hbound G χ Y _ hY hR
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

theorem deleted_discarded_negligible (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))
      (S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)(η ηi χ : Character)(Q X Z : ℝ),
      1≤Z → 0<Q → 0<X → Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
      let F := fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x
      (∀D∈S.powerset,Summable (fun I : SmoothIdeal S=>coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0)) ∧
      ‖∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
          (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := discarded_negligible xi saving L Cscale hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound epsilon hepsilon
  refine ⟨H,D*C,mul_pos hD hC,?_⟩
  intro G S hS η ηi χ Q X Z hZ hQ hX hcap
  dsimp only
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hh := hDb S hS η ηi
    (fun E I=>HeckeDyadic.polynomial χ false
      (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm I.val)) 0 0)
    (C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving)) (by positivity) (by
      intro E hE I
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) I Q X (Cscale*Z^L) hQ hX hcap
      exact hCb G χ _ Z hZ hy.1 hy.2)
  exact ⟨hh.1,hh.2.trans_eq (by ring)⟩

def retainedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    finiteAnnularColumn χ.inverse (paperRadialFourier G) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))

def discardedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    HeckeDyadic.polynomial χ.inverse false (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x)
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0

lemma retainedSchwartz_eq (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) (hX : 0<X) :
    retainedSchwartz χ ψ G X R=
      let S := redundantSet χ.modulus ψ.modulus
      ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
        HeckeDyadic.polynomial χ.inverse false (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0 := by
  unfold retainedSchwartz
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro I
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    ((Finset.mem_powerset.mp hD) hP))
  have hI := norm_pos I.val
  rw [finiteAnnularColumn_eq _ _ (reflected_decayTwo G) _ _ (by positivity)]

lemma restoration_summable (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) (hX : 0<X) :
    let S := redundantSet χ.modulus ψ.modulus
    ∀D∈S.powerset,
      Summable (fun I : SmoothIdeal S=>coefficient ψ ψ.inverse S D I*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) R
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))) ∧
      Summable (fun I : SmoothIdeal S=>coefficient ψ ψ.inverse S D I*
        HeckeDyadic.polynomial χ.inverse false
          (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0) := by
  dsimp only
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := reflected_decayTwo G
  have hr := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  refine ⟨hr.congr ?_,hd⟩
  intro I
  have hN := subset_product_norm_pos D (fun P hP=>hS P ((Finset.mem_powerset.mp hD) hP))
  have hI := norm_pos I.val
  rw [finiteAnnularColumn_eq _ _ hF _ _ (by positivity)]

theorem original_split (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X R : ℝ),0<X →
        HeckeDyadic.polynomial χ false G X 0 0=
          g*(retainedSchwartz χ ψ G X R+discardedSchwartz χ ψ G X R) := by
  obtain ⟨ψ,g,hp,hnp,hg,hcap,h⟩ := original_retained_reflection χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X R hX
  rw [retainedSchwartz_eq χ ψ G X R hX]
  exact h G X R hX

theorem actual_original_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X Z : ℝ),0<X → 1≤Z →
        (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        ‖HeckeDyadic.polynomial χ false G X 0 0-
          g*retainedSchwartz χ ψ G X (Z^(xi/2))‖≤
          C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(χ.modulus.absNorm:ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := deleted_discarded_negligible xi saving L Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,hC,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hsplit⟩ := original_split χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  rw [hsplit G X (Z^(xi/2)) hX,mul_add,add_sub_cancel_left,norm_mul,hg,one_mul]
  have hb := (hCb G S hS ψ ψ.inverse χ.inverse _ X Z hZ hQ hX hcap').2
  apply hb.trans
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hepsilon.le

lemma retainedSchwartz_uniformTwisted (χ ψ : Character) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t X R : ℝ) :
    retainedSchwartz χ ψ (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) X R=
      retainedOriginal χ ψ W X R t := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold retainedSchwartz retainedOriginal
  rw [he]

theorem actual_twisted_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(ha : 0<a)(hs : Function.support W⊆Set.Icc a b)
        (hW : ContDiff ℝ ∞ W)(t X Z : ℝ),0<X → 1≤Z →
        (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
          g*retainedOriginal χ ψ W X (Z^(xi/2)) t‖≤
          C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)*
            (χ.modulus.absNorm:ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,hC,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hbound⟩ := hb χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro W a b ha hs hW t X Z hX hZ hmod
  have hh := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) X Z hX hZ hmod
  rw [retainedSchwartz_uniformTwisted] at hh
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have ht := CenteredMomentTwistedReflection.polynomial_twisted_source χ W X t hX
  rw [←he] at ht
  rw [←ht] at hh
  exact hh

theorem detector_original_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀reverse : Bool,∀k : ℕ,k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t X Z : ℝ,
        0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        let G := CenteredMomentDetectorDictionary.detectorSchwartz reverse k σ t
        ‖HeckeDyadic.polynomial χ false G X 0 0-
          g*retainedSchwartz χ ψ G X (Z^(xi/2))‖≤
          C*(χ.modulus.absNorm:ℝ)^epsilon*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale epsilon hxi hscale hepsilon
  obtain ⟨n,D,hD,hcontrol⟩ := CenteredMomentDetectorDictionary.detectorSchwartz_uniform H
  refine ⟨n,C*D,mul_pos hC hD,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hbound⟩ := hb χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro reverse k hk σ hσ t X Z hX hZ hmod
  dsimp only
  apply (hbound _ X Z hX hZ hmod).trans
  have he := hcontrol reverse k hk σ hσ t
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) (by positivity :
      0≤(χ.modulus.absNorm:ℝ)^epsilon)) (by positivity : 0≤Z^(-saving))
  exact hh.trans_eq (by ring)

end SevenEighths.CenteredMomentUniformReflectionApproximation

end

end OAI
