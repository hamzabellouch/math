import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.FixedWindowCost

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B C : Type*}

lemma blockWindow_word [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (e : X → X) (q : X → A) {k t R : ℕ} (x : X) (i : Fin (k-2*R)) :
    blockWindow (word e q (k+t) x) i=word e q (2*R+1) (e^[i.val] x) := by
  funext j
  simp only [blockWindow,word]
  rw [Nat.add_comm i.val j.val,Function.iterate_add_apply]

lemma integrable_wordCost [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X → X) (he : Measurable e)
    (p : X → C) (q : X → A) (hp : Measurable p) (hq : Measurable q) (k n : ℕ)
    (c : (Fin k → C) → (Fin n → A) → ℝ) :
    Integrable (fun x => c (word e p k x) (word e q n x)) μ :=
  integrable_finite_observation μ (fun x => (word e p k x,word e q n x))
    ((word_measurable e he p hp k).prodMk (word_measurable e he q hq n)) (fun a => c a.1 a.2)

lemma fixedWindowCost_scale [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    {k t R : ℕ} (hn : 0<k+t) (F : C → A) (H : C → B)
    (D : (Fin (2*R+1) → A) → B) (a : Fin k → C) (b : Fin (k+t) → A) :
    2*(k+t : ℕ)*fixedWindowCost F H D a b=prefixNameCost F a b+decoderNameCost H D a b := by
  unfold fixedWindowCost
  exact mul_div_cancel₀ _ (by positivity : (2*((k+t : ℕ) : ℝ))≠0)

variable [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]

theorem fixed_window_tower_bounds (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    {k t R : ℕ} (hn : 0<k+t) (hR : 2*R≤k)
    (hd : Pairwise (fun i j : Fin (k+t) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (p : X → C) (q : X → A) (hp : Measurable p) (hq : Measurable q)
    (F : C → A) (H : C → B) (D : (Fin (2*R+1) → A) → B) :
    let I := ∫ x in U,fixedWindowCost F H D (word e p k x) (word e q (k+t) x) ∂μ
    (μ.real {x | F (p x)≠q x}≤μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ+
      (t : ℝ)/(k+t : ℕ)+2*(k+t : ℕ)*I) ∧
    (μ.real {x | H (p (e^[R] x))≠D (word e q (2*R+1) x)}≤
      μ.real (⋃ i : Fin (k+t),(e^[i.val]) '' U)ᶜ+
      ((t+2*R : ℕ) : ℝ)/(k+t : ℕ)+2*(k+t : ℕ)*I) := by
  intro I
  have hc := integrable_wordCost (μ.restrict U) e e.measurable p q hp hq k (k+t) (fixedWindowCost F H D)
  have hpref := integrable_wordCost (μ.restrict U) e e.measurable p q hp hq k (k+t) (prefixNameCost F)
  have hdec := integrable_wordCost (μ.restrict U) e e.measurable p q hp hq k (k+t) (decoderNameCost H D)
  have hscale : (∫ x in U,prefixNameCost F (word e p k x) (word e q (k+t) x) ∂μ)+
      (∫ x in U,decoderNameCost H D (word e p k x) (word e q (k+t) x) ∂μ)=2*(k+t : ℕ)*I := by
    rw [←integral_add hpref hdec]
    change (∫ x in U,prefixNameCost F (word e p k x) (word e q (k+t) x)+decoderNameCost H D (word e p k x) (word e q (k+t) x) ∂μ)=_
    simp_rw [←fixedWindowCost_scale hn F H D]
    exact integral_const_mul _ _
  have hpre0 := integral_nonneg (f:=fun x => prefixNameCost F (word e p k x) (word e q (k+t) x)) (fun x => prefixNameCost_nonneg F (word e p k x) (word e q (k+t) x)) (μ:=μ.restrict U)
  have hdec0 := integral_nonneg (f:=fun x => decoderNameCost H D (word e p k x) (word e q (k+t) x)) (fun x => decoderNameCost_nonneg H D (word e p k x) (word e q (k+t) x)) (μ:=μ.restrict U)
  constructor
  · have hb := tower_error_integral μ e he hU k (F ∘ p) q ((measurable_of_countable F).comp hp) hq
    have hc := tower_interior_compl_bound μ e he hU hn (show t≤k+t by omega) hd
    have hsub : k+t-t=k := by omega
    rw [hsub] at hc
    change μ.real {x | F (p x)≠q x}≤μ.real (⋃ i : Fin k,(e^[i.val]) '' U)ᶜ+
      ∫ x in U,prefixNameCost F (word e p k x) (word e q (k+t) x) ∂μ at hb
    linarith
  · have hH : Measurable (fun x => H (p (e^[R] x))) := (measurable_of_countable H).comp (hp.comp (e.measurable.iterate _))
    have hD : Measurable (fun x => D (word e q (2*R+1) x)) := (measurable_of_countable D).comp (word_measurable e e.measurable q hq _)
    have hb := tower_error_integral μ e he hU (k-2*R) _ _ hH hD
    have hc := tower_interior_compl_bound μ e he hU hn (show t+2*R≤k+t by omega) hd
    have hsub : k+t-(t+2*R)=k-2*R := by omega
    rw [hsub] at hc
    have heq (x : X) : (∑ i : Fin (k-2*R),symbolCost (H (p (e^[R] (e^[i.val] x))))
        (D (word e q (2*R+1) (e^[i.val] x))))=decoderNameCost H D (word e p k x) (word e q (k+t) x) := by
      unfold decoderNameCost
      apply Finset.sum_congr rfl
      intro i _
      rw [blockWindow_word]
      dsimp only [blockCenter,word]
      rw [Nat.add_comm i.val R,Function.iterate_add_apply]
    simp only [heq] at hb
    linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] [Nonempty C]

theorem actual_fixed_window_copy (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → C) (hp : Measurable p) (F : C → A) (H : C → B)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (hrate : rate μ e p≤weightEntropy β)
    (zero one : A) (h01 : zero≠one) (l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K r m : ℕ,0 < K ∧ 0 < r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ ∀ W : MatrixCoupling (mass μ (word e p (n*K*m))) (productWordWeight β (n*K*m+n*m)),
        ∃ (q : X → A) (s : ℤ) (M : ℕ) (G : (Fin M → A) → C),Measurable q ∧
          μ.real {x | F (p x)≠q x} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          μ.real {x | H (p (e^[R] x))≠D (word e q (2*R+1) x)} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
          μ.real {x | G (word e q M (integerIterate e s x))≠p x} < ε := by
  have hR0 : (0 : ℝ)≤R := Nat.cast_nonneg R
  have hl0 : (0 : ℝ)≤l := Nat.cast_nonneg l
  let θ := ε/(100*((R : ℝ)+(l : ℝ)+3))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : 100*((R : ℝ)+(l : ℝ)+3)*θ=ε := by dsimp [θ]; field_simp
  have hθ0 : 0≤θ := hθ.le
  obtain ⟨K,r,m,hK,hr,hm,hcopy⟩ := synchronized_cost_producer μ e he.toMeasurePreserving htotal
    p hp β hβ hβsum hβentropy hrate zero one hθ
  obtain ⟨Z,hZ⟩ := exists_nat_gt (max ((2*R : ℕ) : ℝ) (max (l : ℝ) (100*((l : ℝ)+2*R)/ε))+1)
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hcopy,eventually_ge_atTop Z] with n hn hnZ
  obtain ⟨hnpos,hrN,htail,hres,hc⟩ := hn
  have hN : 0 < n*K*m+n*m := lt_trans hr hrN
  have hNreal : (0 : ℝ) < (n*K*m+n*m : ℕ) := Nat.cast_pos.mpr hN
  have hnK : n≤n*K*m := (Nat.le_mul_of_pos_right n hK).trans (Nat.le_mul_of_pos_right (n*K) hm)
  have hnN : n≤n*K*m+n*m := hnK.trans (Nat.le_add_right _ _)
  have hZN : (Z : ℝ)≤(n*K*m+n*m : ℕ) := by exact_mod_cast hnZ.trans hnN
  have hZK : (Z : ℝ)≤(n*K*m : ℕ) := by exact_mod_cast hnZ.trans hnK
  have hRk : 2*R≤n*K*m := by
    have hh : ((2*R : ℕ) : ℝ) < (n*K*m : ℕ) := lt_of_le_of_lt (le_max_left _ _)
      ((lt_trans (lt_add_one _) hZ).trans_le hZK)
    exact_mod_cast hh.le
  have hlN : l < n*K*m+n*m := by
    have hh : (l : ℝ) < (n*K*m+n*m : ℕ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _))
      ((lt_trans (lt_add_one _) hZ).trans_le hZN)
    exact_mod_cast hh
  have hfrac : ((l : ℝ)+2*R)/(n*K*m+n*m : ℕ) < ε/100 := by
    apply (div_lt_iff₀ hNreal).mpr
    have hh : 100*((l : ℝ)+2*R)/ε < (n*K*m+n*m : ℕ) :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _))
        ((lt_trans (lt_add_one _) hZ).trans_le hZN)
    have hh' := (div_lt_iff₀ hε).mp hh
    nlinarith
  have hfracL : (l : ℝ)/(n*K*m+n*m : ℕ) < ε/100 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith only [hR0,hl0]) hNreal.le) hfrac
  have hfracR : (2*(R : ℝ))/(n*K*m+n*m : ℕ) < ε/100 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith only [hR0,hl0]) hNreal.le) hfrac
  refine ⟨hnpos,?_⟩
  intro W
  obtain ⟨E,V,hE,hV⟩ := hc W (fixedWindowCost F H D) (fixedWindowCost_nonneg F H D)
    (fixedWindowCost_le_one hN F H D)
    (((2*R+2 : ℕ) : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(2*(n*K*m+n*m : ℕ)))
    (fun a b => fixedWindowCost_markWord F H D a b r zero one)
  have hmarkbudget : ((2*R+2 : ℕ) : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(2*(n*K*m+n*m : ℕ))≤((R : ℝ)+1)*θ := by
    have hh := mul_le_mul_of_nonneg_left hres.le (by positivity : (0 : ℝ)≤(R : ℝ)+1)
    have heq : ((2*R+2 : ℕ) : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(2*(n*K*m+n*m : ℕ))=
        ((R : ℝ)+1)*((Marker.reserved (n*K*m+n*m) r).card/(n*K*m+n*m : ℕ)) := by
      have h2 : ((2*R+2 : ℕ) : ℝ)=2*((R : ℝ)+1) := by push_cast; ring
      rw [h2]
      field_simp
    rwa [heq]
  have hVcost : V.cost (fixedWindowCost F H D) < W.cost (fixedWindowCost F H D)+((R : ℝ)+2)*θ  := by linarith only [hV,hmarkbudget]
  obtain ⟨U,q,hU,hUp,hq,hd,hcover,hbase,hcost,_hoff,hdecode⟩ := lift_cost_transport μ e he hN hrN p hp F _ V
    (fixedWindowCost F H D) (fixedWindowCost_nonneg F H D) (fixedWindowCost_le_one hN F H D)
    zero one h01 (marked_pushWeight_support _ hr hrN zero one) E (Classical.arbitrary C) hθ
  let I := ∫ x in U,fixedWindowCost F H D (word e p (n*K*m) x) (word e q (n*K*m+n*m) x) ∂μ
  have hI : 2*(n*K*m+n*m : ℕ)*I≤2*(V.cost (fixedWindowCost F H D)+θ) := by
    have hmass := tower_real_mass_le_one μ e he.toMeasurePreserving hU (n*K*m+n*m) hd
    have hc0 := V.cost_nonneg (fixedWindowCost F H D) (fixedWindowCost_nonneg F H D)
    have hh := mul_le_mul_of_nonneg_right hmass (show 0≤V.cost (fixedWindowCost F H D)+θ by linarith)
    have hh' := mul_le_mul_of_nonneg_left hcost hNreal.le
    dsimp [I]
    nlinarith only [hh,hh']
  obtain ⟨hpaint,hfixed⟩ := fixed_window_tower_bounds μ e he.toMeasurePreserving hU hN hRk hd p q hp hq F H D
  let G := Marker.decodeWindow hN hrN zero one (extendPrefixDecoder E (Classical.arbitrary C))
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have hmap : ∀ w,mass (μ.restrict U) (word e q (n*K*m+n*m)) w=
      μ.real U*pushWeight (mass ν (word iidShift (fun z : ℤ → A => z 0) (n*K*m+n*m))) (Marker.markWord r zero one) w := by
    intro w
    simpa only [ν,funext (iid_word_mass β hβ hβsum (n*K*m+n*m))] using hbase w
  have hLaw := marked_tower_short_word_lawClose μ ν e he.toMeasurePreserving iidShift (iidShift_preserving _)
    hU hUp q (fun z : ℤ → A => z 0) hq (measurable_pi_apply 0) hlN hd zero one hmap hcover
  have hLaw' : LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β))
      (θ+(l : ℝ)/(n*K*m+n*m : ℕ)+(l : ℝ)*(Marker.reserved (n*K*m+n*m) r).card/(n*K*m+n*m : ℕ)) := by
    simpa only [ν,iid_word_law] using hLaw
  refine ⟨q,-((n*K*m+n*m : ℕ) : ℤ),2*(n*K*m+n*m),G,hq,?_,?_,?_,?_⟩
  · change _≤_+_+2*(n*K*m+n*m : ℕ)*I at hpaint
    nlinarith only [hpaint,hcover,htail,hI,hVcost,hθeq,hθ,hR0,hl0]
  · have hsplit : ((n*m+2*R : ℕ) : ℝ)/(n*K*m+n*m : ℕ)=
        ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)+2*(R : ℝ)/(n*K*m+n*m : ℕ) := by push_cast; ring
    rw [hsplit] at hfixed
    change _≤_+_+2*(n*K*m+n*m : ℕ)*I at hfixed
    nlinarith only [hfixed,hcover,htail,hI,hVcost,hfracR,hθeq,hθ,hR0,hl0]
  · apply hLaw'.mono
    have hres' := mul_le_mul_of_nonneg_left hres.le (Nat.cast_nonneg l)
    rw [←mul_div_assoc] at hres'
    nlinarith only [hres',hfracL,hθeq,hθ,hR0,hl0]
  · change μ.real {x | Marker.decodeWindow _ _ zero one _ (word e q (2*(n*K*m+n*m))
        (integerIterate e (-((n*K*m+n*m : ℕ) : ℤ)) x))≠p x} < ε
    nlinarith only [hdecode,hE,htail,hθeq,hθ,hR0,hl0]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B C : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Fintype C] [DecidableEq C] [MeasurableSingletonClass C] [Nonempty C]

theorem actual_fixed_window_rate_copy (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → C) (hp : Measurable p) (F : C → A) (H : C → B)
    (R : ℕ) (D : (Fin (2*R+1) → A) → B)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (hrate : rate μ e p≤weightEntropy β)
    (zero one : A) (h01 : zero≠one) (l : ℕ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ K r m : ℕ,0 < K ∧ 0 < r ∧ 0 < m ∧ ∀ᶠ n : ℕ in atTop,
      0 < n ∧ ∀ W : MatrixCoupling (mass μ (word e p (n*K*m))) (productWordWeight β (n*K*m+n*m)),
        ∃ q : X → A,Measurable q ∧
          μ.real {x | F (p x)≠q x} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          μ.real {x | H (p (e^[R] x))≠D (word e q (2*R+1) x)} < 2*W.cost (fixedWindowCost F H D)+ε ∧
          LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
          rate μ e p-ρ < rate μ e q := by
  obtain ⟨η,hη,hsmall⟩ := rate_lower_of_small_window_error (B:=A) μ e he.toMeasurePreserving p hp hρ
  obtain ⟨K,r,m,hK,hr,hm,hn⟩ := actual_fixed_window_copy μ e he htotal p hp F H R D β hβ hβsum
    hβentropy hrate zero one h01 l (lt_min hε hη)
  refine ⟨K,r,m,hK,hr,hm,?_⟩
  filter_upwards [hn] with n hn
  refine ⟨hn.1,?_⟩
  intro W
  obtain ⟨q,s,M,G,hq,hpaint,hfixed,hlaw,hdecode⟩ := hn.2 W
  have heq : mass μ (errorObs p (G ∘ word e q M ∘ integerIterate e s)) true=
      μ.real {x | G (word e q M (integerIterate e s x))≠p x} := by
    simp only [mass,Measure.real]
    congr 2
    ext x
    simp only [mem_preimage,mem_singleton_iff,errorObs,decide_eq_true_eq,
      mem_ofPred_eq,Function.comp_apply]
    exact ne_comm
  refine ⟨q,hq,lt_of_lt_of_le hpaint (add_le_add_right (min_le_left _ _) _),
    lt_of_lt_of_le hfixed (add_le_add_right (min_le_left _ _) _),hlaw.mono (min_le_left _ _),?_⟩
  apply hsmall q hq s M G
  rw [heq]
  exact hdecode.trans_le (min_le_right _ _)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem fixed_decoder_arbitrary_tests (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (p : X → A) (hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0 < weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α)
    (happrox : ∀ ε : ℝ,0 < ε → ∃ r : X → A×B,Measurable r ∧ WeakBernoulliProcess μ e r ∧
      μ.real {x | (p x,α x)≠r x} < ε)
    (zero one : A) (h01 : zero≠one) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,
      ∀ l : ℕ,∀ ε ρ : ℝ,0 < ε → 0 < ρ → ∃ q : X → A,Measurable q ∧
        μ.real {x | p x≠q x} < η ∧
        μ.real {x | α (e^[R] x)≠D (word e q (2*R+1) x)} < η ∧
        LawClose (μ.map (word e q l)) (Measure.pi (fun _ : Fin l => finiteWeightLaw β)) ε ∧
        weightEntropy β-ρ < rate μ e q := by
  classical
  obtain ⟨R,D,s,hs,hfd⟩ := fixed_window_fd_graph μ e he p hp β hβ hβsum hβentropy H hcode α hα
    happrox (by positivity : 0 < η/8)
  let P : X → A×B := fun x => (p x,α x)
  have hP : Measurable P := hp.prodMk hα
  have hrateP : rate μ e P=weightEntropy β := by
    apply le_antisymm (H.upper P hP)
    rw [←rate_of_iid_factor μ e he.toMeasurePreserving p hp β hβ hβsum hcode]
    exact rate_pair_ge_left μ e he.toMeasurePreserving p α hp hα
  refine ⟨R,D,?_⟩
  intro l ε ρ hε hρ
  obtain ⟨K,r,m,hK,_hr,hm,hcopy⟩ := actual_fixed_window_rate_copy μ e he htotal P hP Prod.fst Prod.snd R D
    β hβ hβsum hβentropy (H.upper P hP) zero one h01 l (lt_min hε (half_pos hη)) hρ
  have htend : Tendsto (fun n : ℕ => n*s) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_mul_of_pos_right n hs)
  obtain ⟨n,hn⟩ := (htend.eventually hcopy).exists
  have hN : 0 < n*s*K*m+n*s*m :=
    add_pos (Nat.mul_pos (Nat.mul_pos hn.1 hK) hm) (Nat.mul_pos hn.1 hm)
  have hlen : (n*K*m+n*m)*s=n*s*K*m+n*s*m := by ring
  have hST := hfd (n*K*m+n*m)
  rw [hlen] at hST
  obtain ⟨S,hS⟩ := hST
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  have hRT := lift_joint_graph_transport (k:=n*s*K*m) (t:=n*s*m) μ e e.measurable P hP ν D S
  have hiid : mass ν (word iidShift (fun y : ℤ → A => y 0) (n*s*K*m+n*s*m))=
      productWordWeight β (n*s*K*m+n*s*m) := funext (iid_word_mass β hβ hβsum _)
  rw [hiid] at hRT
  obtain ⟨T,hT⟩ := hRT
  have hcost : T.cost (fixedWindowCost Prod.fst Prod.snd D)≤η/8 :=
    hT.trans ((div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr hS)
  obtain ⟨q,hq,hpaint,hfixed,hlaw,hrate⟩ := hn.2 T
  refine ⟨q,hq,?_,?_,hlaw.mono (min_le_left _ _),?_⟩
  · change μ.real {x | p x≠q x} < _ at hpaint
    linarith only [hpaint,hcost,min_le_right ε (η/2),hη]
  · change μ.real {x | α (e^[R] x)≠D (word e q (2*R+1) x)} < _ at hfixed
    linarith only [hfixed,hcost,min_le_right ε (η/2),hη]
  · rwa [hrateP] at hrate
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A B : Type*} [MeasurableSpace X] [MeasurableSpace B]

lemma disagreement_triangle [MeasurableSpace A]
    (μ : Measure X) [IsFiniteMeasure μ] (p q r : X → A) :
    μ.real {x | p x≠r x}≤μ.real {x | p x≠q x}+μ.real {x | q x≠r x} := by
  apply (measureReal_mono (μ:=μ) (show {x | p x≠r x}⊆{x | p x≠q x} ∪ {x | q x≠r x} from ?_)).trans
  · exact measureReal_union_le _ _
  · intro x hx
    by_cases h : p x=q x
    · exact Or.inr (by simpa only [mem_ofPred_eq,h] using hx)
    · exact Or.inl h

lemma disagreement_symm [MeasurableSpace A] (μ : Measure X) (p q : X → A) :
    μ.real {x | p x≠q x}=μ.real {x | q x≠p x} := by
  congr 1
  ext x
  exact ne_comm

variable [MeasurableSpace A]

lemma sequence_distance_le_sum (μ : Measure X) [IsFiniteMeasure μ]
    (q : ℕ → X → A) (η : ℕ → ℝ) (hη : ∀ n,μ.real {x | q n x≠q (n+1) x}≤η n) (n : ℕ) :
    μ.real {x | q 0 x≠q n x}≤∑ j∈Finset.range n,η j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (disagreement_triangle μ (q 0) (q n) (q (n+1))).trans (add_le_add ih (hη n))

lemma partition_limit_distance_bound [MeasurableEq A]
    (μ : Measure X) [IsFiniteMeasure μ] (q : ℕ → X → A) (p r : X → A)
    (hq : ∀ n,Measurable (q n)) (hp : Measurable p)
    (hlim : ∀ᵐ x ∂μ,∀ᶠ n : ℕ in atTop,q n x=p x)
    {δ : ℝ} (hδ : ∀ n,μ.real {x | r x≠q n x}≤δ) :
    μ.real {x | r x≠p x}≤δ := by
  have hz := measureReal_tendsto_zero_of_ae_eventually_notMem μ
    (fun n => {x | q n x≠p x}) (fun n => (measurableSet_eq_fun (hq n) hp).compl)
    (hlim.mono (fun x hx => hx.mono (fun n hn => by simpa using hn)))
  have ht : Tendsto (fun n => μ.real {x | r x≠p x}-μ.real {x | q n x≠p x}) atTop
      (𝓝 (μ.real {x | r x≠p x})) := by simpa using tendsto_const_nhds.sub hz
  apply le_of_tendsto ht
  filter_upwards [] with n
  have h := disagreement_triangle μ r (q n) p
  linarith [hδ n]

lemma finite_decoder_perturbation [StandardBorelSpace X] [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsFiniteMeasure μ] (e : X → X) (he : MeasurePreserving e μ μ)
    (p q : X → A) (hp : Measurable p) (hq : Measurable q)
    (α : X → B) (n : ℕ) (D : (Fin n → A) → B) :
    μ.real {x | α x≠D (word e q n x)}≤μ.real {x | α x≠D (word e p n x)}+
      (n : ℝ)*μ.real {x | p x≠q x} := by
  classical
  apply (disagreement_triangle μ α (D ∘ word e p n) (D ∘ word e q n)).trans
  apply add_le_add_right
  have hsub : {x | (D ∘ word e p n) x≠(D ∘ word e q n) x}⊆{x | word e p n x≠word e q n x} := by
    intro x h heq
    exact h (congrArg D heq)
  exact (measureReal_mono (μ:=μ) hsub).trans
    (word_disagreement_le μ e he p q hp hq n)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal NNReal Topology
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]

theorem seeded_exact_iid_limit (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (e^[m]) μ)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1)
    (hβentropy : 0 < weightEntropy β) (H : FiniteRateSupremum μ e (weightEntropy β))
    (zero one : A) (h01 : zero≠one) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ,∃ δ : ℝ,0 < δ ∧ ∀ q₀ : X → A,Measurable q₀ →
      LawClose (μ.map (word e q₀ L)) (Measure.pi (fun _ : Fin L => finiteWeightLaw β)) δ →
      weightEntropy β-δ≤rate μ e q₀ →
      ∃ p : X → A,Measurable p ∧
        MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
        μ.real {x | q₀ x≠p x} < ε := by
  let θ : ℝ := min (ε/4) (1/4)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθε : 2*θ < ε := by have hh := min_le_left (ε/4) (1/4 : ℝ); dsimp [θ]; linarith
  have hθ1 : θ≤1 := (min_le_right _ _).trans (by norm_num)
  let η : ℕ → ℝ := fun n => θ*(1/2 : ℝ)^n
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hT (n : ℕ) : Nonempty (IIDCopyTest μ e β (η n/2)) :=
    exists_iidCopyTest μ e he.toMeasurePreserving β hβ hβsum hβentropy (half_pos (hη n))
  let T (n : ℕ) : IIDCopyTest μ e β (η n/2) := Classical.choice (hT n)
  refine ⟨max (T 0).length 0,min (T 0).tolerance 1,lt_min (T 0).tolerance_pos zero_lt_one,?_⟩
  intro q₀ hq₀ hl₀ hr₀
  have hg₀ : GoodIIDStage μ e β (T 0) 0 q₀ := by
    refine ⟨hq₀,?_,hr₀.trans' ?_⟩
    · simpa only [Nat.cast_zero,zero_add,div_one] using hl₀
    · linarith only [min_le_left (T 0).tolerance (1 : ℝ)]
  have hnext (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      ∃ q' : X → A,GoodIIDStage μ e β (T (n+1)) (n+1) q' ∧
        μ.real {x | q.val x≠q' x} < η n :=
    goodIIDStage_next μ e he htotal β hβ hβsum hβentropy H zero one h01 (hη n)
      (T n) (T (n+1)) q.property
  let next (n : ℕ) (q : {q : X → A // GoodIIDStage μ e β (T n) n q}) :
      {q' : X → A // GoodIIDStage μ e β (T (n+1)) (n+1) q'} :=
    ⟨Classical.choose (hnext n q),(Classical.choose_spec (hnext n q)).1⟩
  let z : (n : ℕ) → {q : X → A // GoodIIDStage μ e β (T n) n q} :=
    fun n => Nat.rec (motive:=fun j => {q : X → A // GoodIIDStage μ e β (T j) j q})
      ⟨q₀,hg₀⟩ next n
  let q : ℕ → X → A := fun n => (z n).val
  have hq (n : ℕ) : Measurable (q n) := (z n).property.1
  have hpaint (n : ℕ) : μ.real {x | q n x≠q (n+1) x} < η n :=
    (Classical.choose_spec (hnext n (z n))).2
  have hgeom (n : ℕ) : μ.real {x | q (n+1) x≠q n x} < ((1/2 : ℝ≥0)^n : ℝ) := by
    rw [disagreement_symm]
    apply (hpaint n).trans_le
    change θ*(1/2 : ℝ)^n≤_
    simpa only [NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,one_mul] using
      mul_le_mul_of_nonneg_right hθ1 (by positivity : 0≤(1/2 : ℝ)^n)
  obtain ⟨p,hp,hlim⟩ := exists_partition_limit μ q hq (geometric_repainting_summable μ q hgeom)
  have hlaw (n : ℕ) : LawClose (μ.map (word e (q n) n))
      (Measure.pi (fun _ : Fin n => finiteWeightLaw β)) (1/(n+1 : ℝ)) :=
    (iid_lawClose_prefix μ e (q n) (hq n) β hβ hβsum
      (le_max_right _ _) (z n).property.2.1).mono (min_le_right _ _)
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  have hcode := iid_law_of_growing_forward_words μ e he.toMeasurePreserving q hq p hp hlim
    (finiteWeightLaw β) (fun n => 1/(n+1 : ℝ)) tendsto_one_div_add_atTop_nhds_zero_nat hlaw
  refine ⟨p,hp,hcode,lt_of_le_of_lt ?_ hθε⟩
  apply partition_limit_distance_bound μ q p q₀ hq hp hlim
  intro n
  have hh := sequence_distance_le_sum μ q η (fun j => (hpaint j).le) n
  have hsum : (∑ j∈Finset.range n,η j)≤2*θ := by
    simp only [η,←Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hθ.le
    nlinarith only [h]
  exact hh.trans hsum
end HyperbolicCoding

end

end OAI
