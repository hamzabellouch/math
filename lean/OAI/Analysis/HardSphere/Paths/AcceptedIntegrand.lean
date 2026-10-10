import Mathlib
import OAI.Analysis.HardSphere.Paths.LiftedSkeleton

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma measurable_simpleEncounter {K : ℕ} [NeZero K] (R : ℕ)
    (x y : DiscreteTorus K) :
    Measurable (fun p : SimplePath x y × SimplePath x y ↦ simpleEncounter R p.1 p.2) :=
  measurable_of_countable _

lemma measurable_simpleEncounter_comp {Ω : Type*} [MeasurableSpace Ω]
    {K : ℕ} [NeZero K] (R : ℕ) {x y : DiscreteTorus K}
    (f : Ω → SimplePath x y) (hf : Measurable f) :
    Measurable (fun z : Ω×Ω ↦ simpleEncounter (K:=K) R (x:=x) (y:=y) (f z.1) (f z.2)) :=
  by
    have hf1 : Measurable (fun z : Ω×Ω ↦ f z.1) := hf.comp measurable_fst
    have hf2 : Measurable (fun z : Ω×Ω ↦ f z.2) := hf.comp measurable_snd
    have hpair : Measurable (fun z : Ω×Ω ↦ (f z.1,f z.2)) := hf1.prodMk hf2
    exact Measurable.comp
      (g:=fun p : SimplePath x y × SimplePath x y ↦ simpleEncounter (K:=K) R p.1 p.2)
      (f:=fun z : Ω×Ω ↦ (f z.1,f z.2))
      (measurable_simpleEncounter (K:=K) R x y) hpair

@[fun_prop] lemma measurable_dyadicEncounter {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    Measurable (fun z : Noise×Noise ↦ simpleEncounter R
      (dyadicDetour hK R hn d v B hB z.1) (dyadicDetour hK R hn d v B hB z.2)) := by
  exact measurable_simpleEncounter_comp R (dyadicDetour hK R hn d v B hB)
    (measurable_dyadicDetour hK R hn d v B hB)

def acceptedIntegrand {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (κ : ℝ) (B : Finset (DiscreteTorus K)) (z : Noise×Noise) : ℝ≥0∞ :=
  if hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1]) then
    ENNReal.ofReal (Real.exp (κ*(simpleEncounter R (dyadicDetour hK R hn d v B hB z.1)
      (dyadicDetour hK R hn d v B hB z.2):ℝ))) else 0

@[fun_prop] lemma measurable_acceptedIntegrand {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (κ : ℝ) (B : Finset (DiscreteTorus K)) :
    Measurable (acceptedIntegrand hK R hn d v κ B) := by
  unfold acceptedIntegrand
  split_ifs <;> fun_prop

lemma dyadic_environment_moment {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (hnK : 8*n≤K) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (μ : PMF (Finset (DiscreteTorus K))) (p κ : ℝ)
    (hp : 0≤p) (hκ : 0≤κ) (hbad : JointBadLaw μ (ENNReal.ofReal p))
    (hq : ((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ))))*Real.exp 1≤1/2)
    (z : Noise×Noise) :
    (∑' B, μ B*acceptedIntegrand hK R hn d v κ B z)≤
      ENNReal.ofReal (Real.exp (Real.exp 1*((encounterConstant R:ℝ)*κ+
        2*((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ)))))*
          ∑ j∈Finset.range (n+1), Real.exp
            (-twoCopyDistance (min j (n-j)) z/(dyadicRadius R:ℝ)))) := by
  let E (B : Finset (DiscreteTorus K)) := acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])
  let J (B : Finset (DiscreteTorus K)) : ℝ := if hB : E B then
    (simpleEncounter R (dyadicDetour hK R hn d v B hB z.1)
      (dyadicDetour hK R hn d v B hB z.2):ℝ) else 0
  have he (B : Finset (DiscreteTorus K)) : acceptedIntegrand hK R hn d v κ B z=
      if E B then ENNReal.ofReal (Real.exp (κ*J B)) else 0 := by
    change (if hB : E B then ENNReal.ofReal (Real.exp (κ*
      (simpleEncounter R (dyadicDetour hK R hn d v B hB z.1)
        (dyadicDetour hK R hn d v B hB z.2):ℝ))) else 0)=_
    by_cases hB : E B
    · simp only [dite_eq_left hB,ite_eq_left hB,J]
    · simp only [dite_eq_right hB,ite_eq_right hB]
  simp_rw [he]
  refine (accepted_charge_environment_bound R μ p κ (encounterConstant R)
    ((encounterSet (torusNear K R) (projectedSkeleton K n d v z.1)
      (projectedSkeleton K n d v z.2)).card:ℝ) hp hκ hbad
    (projectedSkeleton K n d v z.1) (projectedSkeleton K n d v z.2) E J ?_).trans ?_
  · intro B hB
    simp only [J,dite_eq_left hB]
    exact dyadicDetour_charge hK R hn d v B hB z.1 z.2
  · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (dyadic_nominal_potential R hn hnK d hd v z.1 z.2 κ
        (p*Real.exp (κ*(encounterConstant R:ℝ))) hκ (by positivity) hq))

lemma dyadic_annealed_moment {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (hnK : 8*n≤K) (d : Fin 2 → ℤ) (hd : ∀j, |d j|≤n)
    (v : Vertex) (μ : PMF (Finset (DiscreteTorus K))) (p κ ξ : ℝ)
    (hp : 0≤p) (hκ : 0≤κ) (hbad : JointBadLaw μ (ENNReal.ofReal p))
    (hq : ((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ))))*Real.exp 1≤1/2)
    (hc : 2*(Real.exp 1*((encounterConstant R:ℝ)*κ+
      2*((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ))))))≤ξ)
    (hξ : ∀ T : ℕ, (∫⁻ z, ENNReal.ofReal (Real.exp (ξ*
      ∑ u∈Finset.range (T+1),Real.exp (-twoCopyDistance u z/(dyadicRadius R:ℝ)))) ∂law.prod law)≤2) :
    (∑' B, μ B*∫⁻ z, acceptedIntegrand hK R hn d v κ B z ∂law.prod law)≤2 := by
  have hme (B : Finset (DiscreteTorus K)) : Measurable (fun z ↦ μ B*acceptedIntegrand hK R hn d v κ B z) := by fun_prop
  simp_rw [← lintegral_const_mul' _ _ (PMF.apply_ne_top μ _)]
  rw [← lintegral_tsum (fun B ↦ (hme B).aemeasurable)]
  refine le_trans (lintegral_mono (fun z ↦ ?_)) (hξ (n/2))
  refine (dyadic_environment_moment hK R hn hnK d hd v μ p κ hp hκ hbad hq z).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  let c : ℝ := Real.exp 1*((encounterConstant R:ℝ)*κ+
      2*((candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ)))))
  have hc0 : 0≤c := by dsimp [c]; positivity
  have hf := folded_sum_le n (fun u ↦ Real.exp (-twoCopyDistance u z/(dyadicRadius R:ℝ)))
    (fun _ ↦ (Real.exp_pos _).le)
  calc
    _ ≤ c*(2*∑ u∈Finset.range (n/2+1),Real.exp (-twoCopyDistance u z/(dyadicRadius R:ℝ))) :=
      mul_le_mul_of_nonneg_left hf hc0
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right (by simpa [mul_comm,c] using hc)
      exact Finset.sum_nonneg fun u _ ↦ (Real.exp_pos _).le

lemma small_route_parameters (C A ξ : ℝ) (hC : 0<C) (hA : 0<A) (hξ : 0<ξ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∀ p : ℝ, 0≤p → p≤p₀ →
      (A*(p*Real.exp (κ*C)))*Real.exp 1≤1/2 ∧
      2*(Real.exp 1*(C*κ+2*(A*(p*Real.exp (κ*C)))))≤ξ := by
  let e := Real.exp 1
  let s := min 1 ξ
  let κ := min 1 (s/(16*e*C))
  let p₀ := s/(16*e*A*Real.exp C)
  have he : 0<e := Real.exp_pos _
  have hs : 0<s := lt_min (by norm_num) hξ
  have hs1 : s≤1 := min_le_left _ _
  have hsξ : s≤ξ := min_le_right _ _
  have hκ : 0<κ := lt_min (by norm_num) (div_pos hs (by positivity))
  have hp₀ : 0<p₀ := div_pos hs (by positivity)
  have hκ1 : κ≤1 := min_le_left _ _
  have hκs : e*(C*κ)≤ s/16 := by
    have h := (le_div_iff₀ (by positivity : 0<16*e*C)).mp
      (show κ≤ s/(16*e*C) from min_le_right _ _)
    nlinarith
  refine ⟨p₀,κ,hp₀,hκ,?_⟩
  intro p hp hpp
  have hpbound := (le_div_iff₀ (by positivity : 0<16*e*A*Real.exp C)).mp hpp
  have hexp : Real.exp (κ*C)≤Real.exp C := Real.exp_le_exp.mpr (by nlinarith)
  have hqmon := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hexp hp) hA.le
  have hqe : e*(A*(p*Real.exp (κ*C)))≤ s/16 := by
    have hh := mul_le_mul_of_nonneg_left hqmon he.le
    nlinarith
  constructor
  · change _*e≤_
    nlinarith
  · change 2*(e*(C*κ+2*(A*(p*Real.exp (κ*C)))))≤ξ
    nlinarith

lemma dyadic_path_constants (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ n : ℕ, ∀ hn : 0<n, 8*n≤K → ∀ d : Fin 2 → ℤ, (∀j, |d j|≤n) →
      ∀ v : Vertex, ∀ μ : PMF (Finset (DiscreteTorus K)), ∀ p : ℝ,
      0≤p → p≤p₀ → JointBadLaw μ (ENNReal.ofReal p) →
      (1/2:ℝ≥0∞)≤(∑' B, if acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1]) then μ B else 0) ∧
      ∃ hK : 2<K, (∑' B, μ B*∫⁻ z, acceptedIntegrand hK R hn d v κ B z ∂law.prod law)≤2 := by
  obtain ⟨ξ,hξ,hsoft⟩ := two_copy_soft_moment (dyadicRadius R) (by exact_mod_cast dyadicRadius_pos R)
  obtain ⟨p₁,κ,hp₁,hκ,hparam⟩ := small_route_parameters (encounterConstant R) (candidateConstant (R+2)) ξ
    (by unfold encounterConstant; positivity) (by unfold candidateConstant; positivity) hξ
  obtain ⟨p₂,hp₂,K₀,haccept⟩ := acceptedEnvironment_mass (R+2) (by omega)
  refine ⟨min p₁ p₂,κ,lt_min hp₁ hp₂,hκ,max K₀ 3,?_⟩
  intro K hK inst n hn hnK d hd v μ p hp hpp hbad
  have hK3 : 2<K := by omega
  have hb := hparam p hp (hpp.trans (min_le_left _ _))
  exact ⟨haccept K ((le_max_left _ _).trans hK) inst μ p hp
    (hpp.trans (min_le_right _ _)) hbad v _,hK3,
    dyadic_annealed_moment hK3 R hn hnK d hd v μ p κ ξ hp hκ.le hbad hb.1 hb.2 hsoft⟩

lemma double_lintegral_map {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → X) (hf : Measurable f)
    (g : X×X → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, g (x,y) ∂P.map f ∂P.map f)=
      ∫⁻ z, g (f z.1,f z.2) ∂P.prod P := by
  let : IsProbabilityMeasure (P.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  rw [← lintegral_prod g hg.aemeasurable,Measure.map_prod_map P P hf hf,
    lintegral_map hg (hf.prodMap hf)]
  rfl

lemma dyadicDetour_good_mass {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    (law.map (dyadicDetour hK R hn d v B hB)) {q | simplePathGood B q}=1 := by
  rw [Measure.map_apply (measurable_dyadicDetour hK R hn d v B hB) MeasurableSet.of_discrete]
  have he : (dyadicDetour hK R hn d v B hB) ⁻¹' {q | simplePathGood B q}=Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω x hx
    exact (dyadicDetour_spec hK R hn d v B hB ω x hx).1
  rw [he,measure_univ]

lemma dyadicDetour_double_moment {K n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ) (hn : 0<n)
    (d : Fin 2 → ℤ) (v : Vertex) (κ : ℝ) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])) :
    (∫⁻ q, ∫⁻ q', ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ)))
      ∂law.map (dyadicDetour hK R hn d v B hB) ∂law.map (dyadicDetour hK R hn d v B hB))=
      ∫⁻ z, acceptedIntegrand hK R hn d v κ B z ∂law.prod law := by
  rw [double_lintegral_map law _ (measurable_dyadicDetour hK R hn d v B hB)
    (fun p ↦ ENNReal.ofReal (Real.exp (κ*(simpleEncounter R p.1 p.2:ℝ)))) (measurable_of_countable _)]
  apply lintegral_congr
  intro z
  simp only [acceptedIntegrand,dite_eq_left hB]

theorem dyadic_good_paths_lift (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ {Ω : Type*} [MeasurableSpace Ω], ∀ P : Measure Ω, ∀ _ : IsProbabilityMeasure P,
      ∀ b : Ω → Finset (DiscreteTorus K), Measurable b →
      ∀ p : ℝ, 0≤p → p≤p₀ →
      (∀ A : Finset (DiscreteTorus K), P {d | A⊆b d}≤(ENNReal.ofReal p)^A.card) →
      ∀ n : ℕ, 0<n → 8*n≤K → ∀ d : Fin 2 → ℤ, (∀j, |d j|≤n) → ∀ v : Vertex,
      ∃ E : Set Ω, MeasurableSet E ∧ (1/2:ℝ≥0∞)≤P E ∧
      ∃ ν : Kernel Ω (SimplePath (torusProjection K v) (torusProjection K (v+![(n:ℤ),d 0,d 1]))),
        IsMarkovKernel ν ∧
        (∀ e∈E, ν e {q | simplePathGood (b e) q}=1) ∧
        (∫⁻ e, E.indicator (fun e ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν e ∂ν e) e ∂P)≤2 := by
  obtain ⟨p₀,κ,hp₀,hκ,K₀,hall⟩ := dyadic_path_constants R
  refine ⟨p₀,κ,hp₀,hκ,K₀,?_⟩
  intro K hK inst Ω mΩ P hP b hb p hp hpp hbad n hn hnK d hd v
  let := (Measure.isProbabilityMeasure_map_iff (μ:=P) hb.aemeasurable).mpr inferInstance
  let μ := (P.map b).toPMF
  obtain ⟨hmass,hK2,hmoment⟩ := hall K hK inst n hn hnK d hd v μ p hp hpp
    (mapped_bad_law P b hb _ hbad)
  let E (B : Finset (DiscreteTorus K)) := acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1])
  have hex : ∃ B, E B := by
    by_contra hh
    have hh' : ∀ B, ¬E B := not_exists.mp hh
    simp only [show ∀ B, ¬acceptedEnvironment (R+2) B v (v+![(n:ℤ),d 0,d 1]) from hh',
      ite_false,tsum_zero] at hmass
    norm_num at hmass
  obtain ⟨B₀,hB₀⟩ := hex
  let ω₀ : Noise := fun _ ↦ ⟨0,by norm_num,by norm_num⟩
  let q₀ := dyadicDetour hK2 R hn d v B₀ hB₀ ω₀
  let η (B : Finset (DiscreteTorus K)) := if hB : E B then
    law.map (dyadicDetour hK2 R hn d v B hB) else Measure.dirac q₀
  have hη (B : Finset (DiscreteTorus K)) : IsProbabilityMeasure (η B) := by
    dsimp only [η]
    split_ifs
    · exact (Measure.isProbabilityMeasure_map_iff
        (measurable_dyadicDetour hK2 R hn d v B _).aemeasurable).mpr inferInstance
    · infer_instance
  let ν₀ : Kernel (Finset (DiscreteTorus K))
      (SimplePath (torusProjection K v) (torusProjection K (v+![(n:ℤ),d 0,d 1]))) :=
    ⟨η,Measurable.of_discrete⟩
  let ν := ν₀.comap b hb
  refine ⟨{e | E (b e)},hb (t := {B | E B}) MeasurableSet.of_discrete,?_,ν,?_,?_,?_⟩
  · change (1/2:ℝ≥0∞)≤P (b ⁻¹' {B | E B})
    rw [← Measure.map_apply (μ:=P) hb (s:={B | E B}) MeasurableSet.of_discrete,
      ← Measure.toPMF_toMeasure (P.map b),pmf_event_discrete]
    exact hmass
  · exact ⟨fun e ↦ hη (b e)⟩
  · intro e he
    change E (b e) at he
    change η (b e) {q | simplePathGood (b e) q}=1
    simp only [η,dite_eq_left he]
    exact dyadicDetour_good_mass hK2 R hn d v (b e) he
  · have hpoint (e : Ω) :
        {e | E (b e)}.indicator (fun e ↦ ∫⁻ q, ∫⁻ q',
          ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ))) ∂ν e ∂ν e) e =
        ∫⁻ z, acceptedIntegrand hK2 R hn d v κ (b e) z ∂law.prod law := by
      by_cases he : E (b e)
      · rw [Set.indicator_of_mem (s:={e | E (b e)}) (a:=e) he]
        change (∫⁻ q, ∫⁻ q', ENNReal.ofReal (Real.exp (κ*(simpleEncounter R q q':ℝ)))
          ∂η (b e) ∂η (b e))=_
        simp only [η,dite_eq_left he]
        exact dyadicDetour_double_moment hK2 R hn d v κ (b e) he
      · rw [Set.indicator_of_notMem (s:={e | E (b e)}) (a:=e) he]
        change ¬acceptedEnvironment (R+2) (b e) v (v+![(n:ℤ),d 0,d 1]) at he
        simp only [acceptedIntegrand,dite_eq_right he,lintegral_zero]
    simp_rw [hpoint]
    rw [finite_datum_expectation P b hb
      (fun B ↦ ∫⁻ z, acceptedIntegrand hK2 R hn d v κ B z ∂law.prod law)]
    exact hmoment

end HardSphere.DyadicSkeleton
end
end

end OAI
