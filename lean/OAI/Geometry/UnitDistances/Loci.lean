import OAI.Geometry.UnitDistances.Grid

namespace OAI

namespace PlanarUnitDistances.LocusAvoidance
open Polynomial Filter PowerGrowth
attribute [local instance] Classical.propDecidable
variable {K α ι : Type*} [Field K]

noncomputable def zeros (S : Finset α) (z w : α → K) (f : K[X][X]) : Finset α :=
  S.filter fun a => f.eval₂ (evalRingHom (z a)) (w a)=0

lemma zeros_subset (S : Finset α) (z w : α → K) (f : K[X][X]) : zeros S z w f ⊆ S :=
  Finset.filter_subset _ _

lemma zeros_one (S : Finset α) (z w : α → K) : zeros S z w 1=∅ := by
  simp [zeros]

lemma zeros_unit (S : Finset α) (z w : α → K) {f : K[X][X]} (hf : IsUnit f) :
    zeros S z w f=∅ := by
  obtain ⟨p,hp,rfl⟩ := Polynomial.isUnit_iff.mp hf
  obtain ⟨c,hc,rfl⟩ := Polynomial.isUnit_iff.mp hp
  have hc' : c ≠ 0 := hc.ne_zero
  simp [zeros,hc']

theorem exists_maximizer (S : Finset α) (z w : α → K) (D : ℕ) :
    ∃ f : K[X][X], f ≠ 0 ∧ BivariateDegree.size f ≤ D ∧
      ∀ g : K[X][X], g ≠ 0 → BivariateDegree.size g ≤ D →
        (zeros S z w g).card ≤ (zeros S z w f).card := by
  classical
  let A := S.powerset.filter fun T => ∃ f : K[X][X],
    f ≠ 0 ∧ BivariateDegree.size f ≤ D ∧ zeros S z w f=T
  have hA : A.Nonempty := by
    refine ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),?_⟩⟩
    refine ⟨1,one_ne_zero,?_,zeros_one S z w⟩
    simp [BivariateDegree.size]
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image A Finset.card hA
  obtain ⟨f,hf,hd,rfl⟩ := (Finset.mem_filter.mp hT).2
  refine ⟨f,hf,hd,fun g hg hgd => hmax _ ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (zeros_subset S z w g),g,hg,hgd,rfl⟩

lemma size_X : BivariateDegree.size (X : K[X][X])=1 := by
  simp [BivariateDegree.size,Bivariate.swap_Y]

theorem exists_factor_witness (S : Finset α) (z w : α → K) (D : ℕ)
    (f : K[X][X]) (hf : f ≠ 0) (hd : BivariateDegree.size f ≤ D) :
    ∃ g : K[X][X], Irreducible g ∧ BivariateDegree.size g ≤ max D 1 ∧
      (¬IsUnit f → (zeros S z w f).card ≤ max D 1*(zeros S z w g).card) := by
  by_cases hnu : ¬IsUnit f
  · obtain ⟨g,hg,_,hdeg,hcount⟩ := BivariateDegree.irreducible_zero_capture S z w f hf hnu
    refine ⟨g,hg,hdeg.trans (hd.trans (le_max_left _ _)),fun _ => ?_⟩
    exact hcount.trans (Nat.mul_le_mul_right _ (hd.trans (le_max_left _ _)))
  · exact ⟨X,Polynomial.irreducible_X,by rw [size_X]; exact le_max_right _ _,fun h => False.elim (hnu h)⟩

theorem plane_or_curve (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (S : ι → Finset α) (z w : α → K) :
    (∀ D : ℕ, ∃ b : ℝ, 0<b ∧ ∀ᶠ i in U,∀ f : K[X][X],
      f ≠ 0 → BivariateDegree.size f ≤ D →
        ((zeros (S i) z w f).card : ℝ) ≤ t i^(1-b)) ∨
    ∃ D : ℕ,∃ f : ι → K[X][X],
      (∀ i,Irreducible (f i) ∧ BivariateDegree.size (f i) ≤ D) ∧
      Lower (U : Filter ι) t (fun i => ((zeros (S i) z w (f i)).card : ℝ)) 1 := by
  classical
  by_cases hplane : ∀ D : ℕ, ∃ b : ℝ, 0<b ∧ ∀ᶠ i in U,∀ f : K[X][X],
      f ≠ 0 → BivariateDegree.size f ≤ D →
        ((zeros (S i) z w f).card : ℝ) ≤ t i^(1-b)
  · exact Or.inl hplane
  · push Not at hplane
    obtain ⟨D,hD⟩ := hplane
    choose f hf hfd hfm using fun i => exists_maximizer (S i) z w D
    let m : ι → ℝ := fun i => (zeros (S i) z w (f i)).card
    have hm : Lower (U : Filter ι) t m 1 := by
      intro ε hε
      filter_upwards [hD ε hε] with i hi
      obtain ⟨g,hg,hgd,hgc⟩ := hi
      exact hgc.le.trans (Nat.cast_le.mpr (hfm i g hg hgd))
    have hnu : ∀ᶠ i in U,¬IsUnit (f i) := by
      filter_upwards [hm.eventually_pos ht] with i hi hunit
      have hz := zeros_unit (S i) z w hunit
      simp [m,hz] at hi
    choose g hg hgd hgc using fun i => exists_factor_witness (S i) z w D (f i) (hf i) (hfd i)
    have hM : 0<(max D 1 : ℕ) := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hMr : 0<((max D 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hM
    refine Or.inr ⟨max D 1,g,fun i => ⟨hg i,hgd i⟩,?_⟩
    apply (hm.const_mul ht (inv_pos.mpr hMr)).mono
    filter_upwards [hnu] with i hi
    have hc : m i ≤ ((max D 1 : ℕ) : ℝ)*(zeros (S i) z w (g i)).card := by
      dsimp only [m]
      exact_mod_cast hgc i hi
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hMr).mpr (by simpa only [mul_comm] using hc)

lemma eval_swap (f : K[X][X]) (a b : K) :
    (Bivariate.swap f).eval₂ (evalRingHom a) b=f.eval₂ (evalRingHom b) a := by
  simpa only [coe_aevalAeval_eq_evalEval,eval₂_evalRingHom] using
    Bivariate.aevalAeval_swap (R := K) a b f

lemma zeros_swap (S : Finset α) (z w : α → K) (f : K[X][X]) :
    zeros S w z (Bivariate.swap f)=zeros S z w f := by
  simp only [zeros,eval_swap]

lemma size_swap (f : K[X][X]) : BivariateDegree.size (Bivariate.swap f)=BivariateDegree.size f := by
  simp only [BivariateDegree.size,Bivariate.swap_swap_apply,add_comm]

lemma zeros_card_le_of_degree_zero (S : Finset α) (z w : α → K)
    (hz : Set.InjOn z S) (f : K[X][X]) (hf : f ≠ 0) (hd : f.natDegree=0) :
    (zeros S z w f).card ≤ BivariateDegree.size f := by
  classical
  obtain ⟨p,hp⟩ := natDegree_eq_zero.mp hd
  subst f
  have hp0 : p ≠ 0 := fun h => hf (by simp [h])
  have hinj : Set.InjOn z (zeros S z w (C p)) := fun _ hx _ hy he =>
    hz (zeros_subset _ _ _ _ hx) (zeros_subset _ _ _ _ hy) he
  calc
    (zeros S z w (C p)).card = ((zeros S z w (C p)).image z).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ p.natDegree := by
      apply card_le_degree_of_subset_roots
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      apply (mem_roots hp0).mpr
      simpa only [eval₂_C,coe_evalRingHom,IsRoot.def] using
        (Finset.mem_filter.mp hx).2
    _ ≤ BivariateDegree.size (C p) := by
      simp only [BivariateDegree.size,natDegree_C,Bivariate.swap_C,
        natDegree_map_eq_of_injective C_injective,zero_add,le_refl]

lemma both_degrees_pos_of_many_zeros (S : Finset α) (z w : α → K)
    (hz : Set.InjOn z S) (hw : Set.InjOn w S) (f : K[X][X])
    (hf : f ≠ 0) (hc : BivariateDegree.size f < (zeros S z w f).card) :
    0<f.natDegree ∧ 0<(Bivariate.swap f).natDegree := by
  constructor
  · by_contra h
    exact (not_le_of_gt hc) (zeros_card_le_of_degree_zero S z w hz f hf (by omega))
  · by_contra h
    have hs0 : Bivariate.swap f ≠ 0 := fun he =>
      hf (Bivariate.swap.injective (he.trans (map_zero _).symm))
    have hh := zeros_card_le_of_degree_zero S w z hw (Bivariate.swap f) hs0 (by omega)
    rw [zeros_swap,size_swap] at hh
    exact (not_le_of_gt hc) hh

theorem eventually_both_degrees_pos (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (S : ι → Finset α) (z w : α → K)
    (hz : ∀ i,Set.InjOn z (S i)) (hw : ∀ i,Set.InjOn w (S i))
    (f : ι → K[X][X]) (D : ℕ)
    (hf : ∀ᶠ i in U,f i ≠ 0 ∧ BivariateDegree.size (f i) ≤ D)
    (hc : Lower (U : Filter ι) t (fun i => ((zeros (S i) z w (f i)).card : ℝ)) 1) :
    ∀ᶠ i in U,0<(f i).natDegree ∧ 0<(Bivariate.swap (f i)).natDegree := by
  have hh := (hc.tendsto_atTop ht zero_lt_one).eventually_gt_atTop (D : ℝ)
  filter_upwards [hf,hh] with i hi hcount
  apply both_degrees_pos_of_many_zeros (S i) z w (hz i) (hw i) (f i) hi.1
  exact hi.2.trans_lt (Nat.cast_lt.mp hcount)

end PlanarUnitDistances.LocusAvoidance

namespace PlanarUnitDistances.PlaneIntersection
open Polynomial

variable {K : Type*} [Field K]

lemma resultant_ne_zero_of_irreducible (f g : K[X][X])
    (hf : Irreducible f) (hd : f.natDegree ≠ 0) (hfg : ¬ f ∣ g) :
    f.resultant g ≠ 0 := by
  let φ := algebraMap K[X] (RatFunc K)
  have hi : Irreducible (f.map φ) :=
    (hf.isPrimitive hd).irreducible_iff_irreducible_map_fraction_map.mp hf
  have hnd : ¬ f.map φ ∣ g.map φ := by
    intro hh
    exact hfg ((hf.isPrimitive hd).dvd_iff_fraction_map_dvd_fraction_map (RatFunc K) |>.mpr hh)
  have hr := Polynomial.resultant_ne_zero (f.map φ) (g.map φ)
    (hi.coprime_iff_not_dvd.mpr hnd)
  have hm (p : K[X][X]) : (p.map φ).natDegree=p.natDegree :=
    natDegree_map_eq_of_injective (IsFractionRing.injective K[X] (RatFunc K)) p
  rw [hm f,hm g,resultant_map_map] at hr
  intro hz
  apply hr
  rw [hz,map_zero]

lemma eval_resultant_zero (f g : K[X][X]) (a b : K)
    (hf : f.eval₂ (evalRingHom a) b=0) (hg : g.eval₂ (evalRingHom a) b=0)
    (hd : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) :
    (f.resultant g).eval a=0 := by
  obtain ⟨p,q,_,_,he⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hd
  have hh := congrArg (fun h : K[X][X] => h.eval₂ (evalRingHom a) b) he
  simpa only [eval₂_add,eval₂_mul,eval₂_C,hf,hg,zero_mul,zero_add,coe_evalRingHom] using hh.symm

lemma natDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K[X]) {D : ℕ} (hA : ∀ i j, (A i j).natDegree ≤ D) :
    A.det.natDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro g _
  have hs : (Equiv.Perm.sign g • ∏ i, A (g i) i).natDegree =
      (∏ i, A (g i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h|h
    · rw [h,one_smul]
    · rw [h,Units.neg_smul,one_smul,natDegree_neg]
  rw [hs]
  exact (natDegree_prod_le _ _).trans (by
    calc
      ∑ i, (A (g i) i).natDegree ≤ ∑ _i : ι,D := Finset.sum_le_sum (fun i _ => hA _ _)
      _ = _ := by simp)

lemma natDegree_resultant_le (f g : K[X][X]) {D : ℕ}
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (f.resultant g).natDegree ≤ (f.natDegree+g.natDegree)*D := by
  unfold resultant
  apply (natDegree_det_le _ (D := D) ?_).trans_eq (by simp)
  intro i j
  induction j using Fin.addCases <;>
    simp only [sylvester,Matrix.of_apply,Fin.addCases_left,Fin.addCases_right]
  · split_ifs <;> simp_all only [natDegree_zero,Nat.zero_le]
  · split_ifs <;> simp_all only [natDegree_zero,Nat.zero_le]

theorem intersection_card_le {α : Type*} (S : Finset α) (z w : α → K)
    (hz : Set.InjOn z S) (f g : K[X][X]) (hf : Irreducible f)
    (hd : f.natDegree ≠ 0) (hfg : ¬ f ∣ g) {D : ℕ}
    (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hSf : ∀ a ∈ S, f.eval₂ (evalRingHom (z a)) (w a)=0)
    (hSg : ∀ a ∈ S, g.eval₂ (evalRingHom (z a)) (w a)=0) :
    S.card ≤ (f.natDegree+g.natDegree)*D := by
  classical
  have hres := resultant_ne_zero_of_irreducible f g hf hd hfg
  calc
    S.card = (S.image z).card := (Finset.card_image_of_injOn hz).symm
    _ ≤ (f.resultant g).natDegree := by
      apply card_le_degree_of_subset_roots
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      exact (mem_roots hres).mpr (eval_resultant_zero f g (z x) (w x) (hSf x hx) (hSg x hx) (Or.inl hd))
    _ ≤ _ := natDegree_resultant_le f g hfD hgD

end PlanarUnitDistances.PlaneIntersection

namespace PlanarUnitDistances.RealCurveSymmetry
open Polynomial Filter LocusAvoidance PowerGrowth
attribute [local instance] Classical.propDecidable

lemma coeff_degree_le_swap_degree {K : Type*} [Field K] (f : K[X][X]) (m : ℕ) :
    (f.coeff m).natDegree ≤ (Bivariate.swap f).natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [← BivariateDegree.coeff_swap f n m,coeff_eq_zero_of_natDegree_lt hn,coeff_zero]

lemma degree_le_size {K : Type*} [Field K] (f : K[X][X]) : f.natDegree ≤ BivariateDegree.size f :=
  Nat.le_add_right _ _

lemma coeff_degree_le_size {K : Type*} [Field K] (f : K[X][X]) (m : ℕ) :
    (f.coeff m).natDegree ≤ BivariateDegree.size f :=
  (coeff_degree_le_swap_degree f m).trans (Nat.le_add_left _ _)

noncomputable def conjugate (f : ℂ[X][X]) : ℂ[X][X] :=
  f.map (Polynomial.mapRingHom (starRingEnd ℂ))

noncomputable def reflect (f : ℂ[X][X]) : ℂ[X][X] := Bivariate.swap (conjugate f)

lemma conjugate_injective : Function.Injective conjugate :=
  Polynomial.map_injective _ (Polynomial.map_injective _ star_injective)

lemma conjugate_degree (f : ℂ[X][X]) : (conjugate f).natDegree=f.natDegree :=
  natDegree_map_eq_of_injective (Polynomial.map_injective _ star_injective) f

lemma swap_conjugate (f : ℂ[X][X]) : Bivariate.swap (conjugate f)=conjugate (Bivariate.swap f) := by
  ext m n
  simp only [conjugate,BivariateDegree.coeff_swap,coeff_map,coe_mapRingHom]

lemma reflect_size (f : ℂ[X][X]) : BivariateDegree.size (reflect f)=BivariateDegree.size f := by
  unfold reflect BivariateDegree.size
  rw [Bivariate.swap_swap_apply,swap_conjugate,conjugate_degree,conjugate_degree]
  exact Nat.add_comm _ _

lemma reflect_degree (f : ℂ[X][X]) : (reflect f).natDegree=(Bivariate.swap f).natDegree := by
  rw [reflect,swap_conjugate,conjugate_degree]

lemma reflect_ne_zero {f : ℂ[X][X]} (hf : f ≠ 0) : reflect f ≠ 0 := by
  intro h
  have hh : conjugate f=0 := Bivariate.swap.injective (h.trans (map_zero _).symm)
  exact hf (conjugate_injective (hh.trans (by simp [conjugate])))

lemma reflect_eval (f : ℂ[X][X]) (z : ℂ) :
    (reflect f).eval₂ (evalRingHom z) (star z)=star (f.eval₂ (evalRingHom z) (star z)) := by
  rw [reflect,eval_swap]
  simpa only [conjugate,eval₂_evalRingHom,starRingEnd_apply,star_star] using
    map_mapRingHom_evalEval (starRingEnd ℂ) f z (star z)

theorem reflect_eq_const_mul {α : Type*} (S : Finset α) (z w : α → ℂ)
    (hz : Set.InjOn z S) (hw : ∀ p ∈ S,w p=star (z p))
    (f : ℂ[X][X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0)
    {D : ℕ} (hD : BivariateDegree.size f ≤ D) (hcard : 2*D^2<S.card)
    (hzero : ∀ p ∈ S,f.eval₂ (evalRingHom (z p)) (w p)=0) :
    ∃ c : ℂ,c ≠ 0 ∧ reflect f=f*C (C c) := by
  have hdiv : f ∣ reflect f := by
    by_contra hn
    have hres := PlaneIntersection.intersection_card_le S z w hz f (reflect f) hf hd hn
      (fun m => (coeff_degree_le_size f m).trans hD)
      (fun m => (coeff_degree_le_size (reflect f) m).trans ((reflect_size f).le.trans hD))
      hzero (fun p hp => by rw [hw p hp,reflect_eval,← hw p hp,hzero p hp,star_zero])
    have hfD := (degree_le_size f).trans hD
    have hrD := (degree_le_size (reflect f)).trans ((reflect_size f).le.trans hD)
    have hb : (f.natDegree+(reflect f).natDegree)*D ≤ 2*D^2 := by
      nlinarith
    exact (not_le_of_gt hcard) (hres.trans hb)
  obtain ⟨g,hg⟩ := hdiv
  have hg0 : g ≠ 0 := right_ne_zero_of_mul (hg ▸ reflect_ne_zero hf.ne_zero)
  have hsize : BivariateDegree.size g=0 := by
    have he := BivariateDegree.size_mul hf.ne_zero hg0
    rw [← hg,reflect_size] at he
    omega
  obtain ⟨c,hc⟩ := (BivariateDegree.size_eq_zero_iff g).mp hsize
  refine ⟨c,?_,?_⟩
  · intro hc0
    exact hg0 (by rw [hc,hc0,map_zero,map_zero])
  · rw [hg,hc]

lemma projection_degrees_eq {f : ℂ[X][X]} (hf : f ≠ 0)
    {c : ℂ} (hc : c ≠ 0) (he : reflect f=f*C (C c)) :
    f.natDegree=(Bivariate.swap f).natDegree := by
  have h := congrArg Polynomial.natDegree he
  have hC : (C (C c) : ℂ[X][X]) ≠ 0 := by simpa using hc
  rw [reflect_degree,natDegree_mul hf hC,natDegree_C,Nat.add_zero] at h
  exact h.symm

end PlanarUnitDistances.RealCurveSymmetry

namespace PlanarUnitDistances.UltraCurve
open Polynomial Filter UnitDistances.UltraField UltraPolynomial
variable {ι : Type*} (U : Ultrafilter ι)
abbrev CU := FieldProduct U (fun _ => ℂ)

lemma eval_mk (p : (ι → ℂ)[X][X]) (z w : ι → ℂ) :
    (bimapping (mk U (fun _ => ℂ)) p).eval₂
      (evalRingHom (mk U (fun _ => ℂ) z)) (mk U (fun _ => ℂ) w)=
    mk U (fun _ => ℂ) (fun i => (bimapping (Pi.evalRingHom (fun _ => ℂ) i) p).eval₂
      (evalRingHom (z i)) (w i)) := by
  simp only [eval₂_evalRingHom,bimapping,coe_mapRingHom,map_mapRingHom_evalEval]
  congr 1
  funext i
  exact (map_mapRingHom_evalEval (Pi.evalRingHom (fun _ : ι => ℂ) i) p z w).symm

lemma swap_bimapping {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : R[X][X]) : Bivariate.swap (bimapping φ p)=bimapping φ (Bivariate.swap p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial m c => simp only [bimapping,coe_mapRingHom,map_monomial,
        Bivariate.swap_monomial_monomial]

noncomputable def locus (f : ι → ℂ[X][X]) (D : ℕ) : (CU U)[X][X] :=
  bimapping (mk U (fun _ => ℂ)) (pack (fun _ => ℂ) f D)

lemma pack_eq (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, BivariateDegree.size (f i)≤D) (i : ι) :
    bimapping (Pi.evalRingHom (fun _ => ℂ) i) (pack (fun _ => ℂ) f D)=f i :=
  pack_eval _ f D i ((RealCurveSymmetry.degree_le_size _).trans (hf i))
    (fun m => (RealCurveSymmetry.coeff_degree_le_size _ m).trans (hf i))

lemma locus_irreducible (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, Irreducible (f i) ∧ BivariateDegree.size (f i)≤D) :
    Irreducible (locus U f D) := by
  apply irreducible_of_eventually
  exact Eventually.of_forall fun i => by rw [pack_eq f D (fun i => (hf i).2)]; exact (hf i).1

lemma locus_root (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, BivariateDegree.size (f i)≤D) (p : ι → ℂ)
    (hp : ∀ᶠ i in U,(f i).eval₂ (evalRingHom (p i)) (star (p i))=0) :
    (locus U f D).eval₂ (evalRingHom (mk U (fun _ => ℂ) p))
      (mk U (fun _ => ℂ) (fun i => star (p i)))=0 := by
  rw [locus,eval_mk,mk_eq_zero]
  simpa only [pack_eq f D hf] using hp

lemma locus_degrees (t : ι → ℝ) (ht : Tendsto t (U : Filter ι) atTop)
    (S : ι → Finset ℂ) (hS : PowerGrowth.Lower (U : Filter ι) t (fun i => (S i).card) 1)
    (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, Irreducible (f i) ∧ BivariateDegree.size (f i)≤D)
    (hz : ∀ᶠ i in U,∀ p∈S i,(f i).eval₂ (evalRingHom p) (star p)=0) :
    (locus U f D).natDegree≠0 ∧
    (Bivariate.swap (locus U f D)).natDegree=(locus U f D).natDegree := by
  have hzero : ∀ᶠ i in U,LocusAvoidance.zeros (S i) id star (f i)=S i := by
    filter_upwards [hz] with i hi
    exact Finset.filter_eq_self.mpr hi
  have hcount := (hS.congr (Eventually.mono hzero fun i hi => congrArg (fun s : Finset ℂ => (s.card : ℝ)) hi.symm))
  have hp := LocusAvoidance.eventually_both_degrees_pos U t ht S id star
    (fun _ => fun _ _ _ _ h => h) (fun _ => fun _ _ _ _ h => star_injective h) f D
    (Eventually.of_forall fun i => ⟨(hf i).1.ne_zero,(hf i).2⟩) hcount
  have hc := (hS.tendsto_atTop ht zero_lt_one).eventually_gt_atTop ((2*D^2 : ℕ) : ℝ)
  have hsym : ∀ᶠ i in U,(Bivariate.swap (f i)).natDegree=(f i).natDegree := by
    filter_upwards [hz,hp,hc] with i hi hpi hci
    obtain ⟨c,hcn,he⟩ := RealCurveSymmetry.reflect_eq_const_mul (S i) id star
      (fun _ _ _ _ h => h) (fun _ _ => rfl) (f i) (hf i).1 (by omega) (hf i).2
      (Nat.cast_lt.mp hci) hi
    exact (RealCurveSymmetry.projection_degrees_eq (hf i).1.ne_zero hcn he).symm
  have hdeg := eventually_outer_degree U (fun _ => ℂ) (pack (fun _ => ℂ) f D)
  have hswap := eventually_outer_degree U (fun _ => ℂ) (Bivariate.swap (pack (fun _ => ℂ) f D))
  simp only [← swap_bimapping,pack_eq f D (fun i => (hf i).2)] at hdeg hswap
  obtain ⟨i,hpi,hsi,hdi,hswi⟩ := (hp.and (hsym.and (hdeg.and hswap))).exists
  change (locus U f D).natDegree≠0 ∧ _
  change (f i).natDegree=(locus U f D).natDegree at hdi
  change (Bivariate.swap (f i)).natDegree=(Bivariate.swap (locus U f D)).natDegree at hswi
  constructor
  · omega
  · exact hswi.symm.trans (hsi.trans hdi)

end PlanarUnitDistances.UltraCurve

namespace PlanarUnitDistances.CirclePolynomial
open Polynomial
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

noncomputable def circle (u v : B) : B[X][X] :=
  (C X-C (C u))*(X-C (C v))-1

@[simp] lemma eval_circle (u v : B) (z w : K) :
    (circle u v).eval₂ (aeval z).toRingHom w=
      (z-algebraMap B K u)*(w-algebraMap B K v)-1 := by
  simp [circle]

lemma circle_ne_zero (u v : B) : circle u v≠0 := by
  intro h
  have hh := congrArg (fun p : B[X][X] => (p.coeff 1).coeff 1) h
  simp [circle,sub_mul,coeff_one] at hh

lemma circle_degree (u v : B) : (circle u v).natDegree=1 := by
  apply Nat.le_antisymm
  · apply (natDegree_sub_le _ _).trans
    apply max_le _ (by simp)
    apply natDegree_mul_le.trans
    have h1 : (C X-C (C u) : B[X][X]).natDegree=0 := by rw [← C_sub]; simp
    have h2 : (X-C (C v) : B[X][X]).natDegree=1 := natDegree_X_sub_C _
    rw [h1,h2]
  · apply le_natDegree_of_ne_zero
    intro h
    have hh := congrArg (fun p : B[X] => p.coeff 1) h
    simp [circle,sub_mul,coeff_one] at hh

lemma swap_circle (u v : B) : Bivariate.swap (circle u v)=circle v u := by
  simp only [circle,map_sub,map_mul,map_one,Bivariate.swap_X,Bivariate.swap_Y,
    Bivariate.swap_C_C]
  ring

lemma circle_size (u v : B) : BivariateDegree.size (circle u v)=2 := by
  simp only [BivariateDegree.size,swap_circle,circle_degree]

theorem eq_mul_const (f : B[X][X]) (hf : Irreducible f)
    (hd : f.natDegree≠0) (hs : (Bivariate.swap f).natDegree≠0)
    (u v : B) (z w : K) (hz : Transcendental B z)
    (hfroot : f.eval₂ (aeval z).toRingHom w=0)
    (hcircle : (z-algebraMap B K u)*(w-algebraMap B K v)=1) :
    ∃ c : B,c≠0 ∧ circle u v=f*C (C c) := by
  have hc : f ∣ circle u v := by
    by_contra hn
    exact CurveSeparation.eval_ne_zero f (circle u v) hf hd hn z w hz hfroot
      (by rw [eval_circle,hcircle,sub_self])
  obtain ⟨q,hq⟩ := hc
  have hq0 : q≠0 := right_ne_zero_of_mul (hq ▸ circle_ne_zero u v)
  have hsize : BivariateDegree.size q=0 := by
    have hh := BivariateDegree.size_mul hf.ne_zero hq0
    rw [← hq,circle_size] at hh
    have hfn : 2≤BivariateDegree.size f := by unfold BivariateDegree.size; omega
    omega
  obtain ⟨c,hc⟩ := (BivariateDegree.size_eq_zero_iff q).mp hsize
  refine ⟨c,?_,?_⟩
  · intro h
    exact hq0 (by rw [hc,h,map_zero,map_zero])
  · rw [hq,hc]
end PlanarUnitDistances.CirclePolynomial

namespace PlanarUnitDistances.ComplexCircle
open Polynomial

theorem centers_conjugate (S : Finset ℂ) (u v : ℂ) (hS : 2<S.card)
    (hroot : ∀ z ∈ S, (z-u)*(star z-v)=1) : v=star u := by
  classical
  by_contra hne
  let A := star v-u
  let B := v-star u
  let C := star u*star v-u*v
  let p : ℂ[X] := Polynomial.C B*X^2+Polynomial.C (C-A*v-u*B)*X+
    Polynomial.C (-u*(C-A*v)-A)
  have hp : p≠0 := by
    intro h
    have hh := congrArg (fun q : ℂ[X] => q.coeff 2) h
    have hb : B=0 := by simpa [p] using hh
    exact hne (sub_eq_zero.mp hb)
  have hd : p.natDegree≤2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le _ (by simp only [natDegree_C]; omega)
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le).trans (by simp only [natDegree_C,natDegree_X_pow,Nat.zero_add]; omega)
    · exact (natDegree_mul_le).trans (by simp only [natDegree_C,natDegree_X,Nat.zero_add]; omega)
  have hz (z : ℂ) (hz : z∈S) : p.eval z=0 := by
    have hh := hroot z hz
    have hs := congrArg star hh
    simp only [star_mul,star_sub,star_star,star_one] at hs
    have hl : A*star z=B*z+C := by
      dsimp only [A,B,C]
      linear_combination hh-hs
    simp only [p,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    linear_combination A*hh-(z-u)*hl
  apply hp
  exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S hz (hd.trans_lt hS)

end PlanarUnitDistances.ComplexCircle

namespace PlanarUnitDistances.UltraCircle
open Polynomial Filter UnitDistances.UltraField UltraPolynomial UltraCurve CirclePolynomial
variable {ι : Type*} (U : Ultrafilter ι)

lemma eventual_equation (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i,BivariateDegree.size (f i)≤D) (u v c : ι → ℂ)
    (he : circle (mk U (fun _ => ℂ) u) (mk U (fun _ => ℂ) v)=
      locus U f D*C (C (mk U (fun _ => ℂ) c))) :
    ∀ᶠ i in U,circle (u i) (v i)=f i*C (C (c i)) := by
  let q : (ι → ℂ)[X][X] := (C X-C (C u))*(X-C (C v))-1
  have h : bimapping (mk U (fun _ => ℂ)) q=
      bimapping (mk U (fun _ => ℂ)) (pack (fun _ => ℂ) f D*C (C c)) := by
    simpa only [q,bimapping,coe_mapRingHom,Polynomial.map_sub,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X,Polynomial.map_one,circle,locus] using he
  have hh := (bimap_eq_iff U (fun _ => ℂ) q _).mp h
  filter_upwards [hh] with i hi
  simpa only [q,circle,map_mul,pack_eq f D hf,bimapping,coe_mapRingHom,
    Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    Polynomial.map_one,Pi.evalRingHom_apply] using hi

lemma mk_circle_iff (z u v : ι → ℂ) :
    (mk U (fun _ => ℂ) z-mk U (fun _ => ℂ) u)*
      (mk U (fun _ => ℂ) (fun i => star (z i))-mk U (fun _ => ℂ) v)=1 ↔
    ∀ᶠ i in U,(z i-u i)*(star (z i)-v i)=1 := by
  rw [← map_sub,← map_sub,← map_mul,← (mk U (fun _ => ℂ)).map_one,mk_eq_mk]
  rfl

lemma real_circle_iff (z u : ℂ) : (z-u)*(star z-star u)=1 ↔ ‖z-u‖=1 := by
  rw [← star_sub]
  change (z-u)*(starRingEnd ℂ) (z-u)=1 ↔ ‖z-u‖=1
  rw [Complex.mul_conj]
  constructor
  · intro h
    have hh : Complex.normSq (z-u)=1 := by exact_mod_cast h
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (z-u)]
  · intro h
    rw [Complex.normSq_eq_norm_sq,h]
    norm_num

theorem forbidden (t : ι → ℝ) (ht : Tendsto t (U : Filter ι) atTop)
    (S P : ι → Finset ℂ) (hsub : ∀ i,S i⊆P i)
    (hS : PowerGrowth.Lower (U : Filter ι) t (fun i => (S i).card) 1)
    (f : ι → ℂ[X][X]) (D : ℕ) (hf : ∀ i,BivariateDegree.size (f i)≤D)
    (hz : ∀ᶠ i in U,∀ z∈S i,(f i).eval₂ (evalRingHom z) (star z)=0)
    (p r u v c : ι → ℂ)
    (he : circle (mk U (fun _ => ℂ) u) (mk U (fun _ => ℂ) v)=
      locus U f D*C (C (mk U (fun _ => ℂ) c)))
    (hp : (mk U (fun _ => ℂ) p-mk U (fun _ => ℂ) u)*
      (mk U (fun _ => ℂ) (fun i => star (p i))-mk U (fun _ => ℂ) v)=1)
    (hr : (mk U (fun _ => ℂ) r-mk U (fun _ => ℂ) u)*
      (mk U (fun _ => ℂ) (fun i => star (r i))-mk U (fun _ => ℂ) v)=1)
    (hno : ∀ᶠ i in U,∀ a : ℂ,
      t i^((9:ℝ)/10)≤((P i).filter (fun z => ‖z-a‖=1)).card →
      ¬(‖p i-a‖=1 ∧ ‖r i-a‖=1)) : False := by
  classical
  have hc := (hS.tendsto_atTop ht zero_lt_one).eventually_gt_atTop (2 : ℝ)
  have hfull := hS (1/10) (by norm_num)
  obtain ⟨i,hei,hzi,hci,hfi,hpi,hri,hni⟩ :=
    ((eventual_equation U f D hf u v c he).and
      (hz.and (hc.and (hfull.and ((mk_circle_iff U p u v).mp hp |>.and
        ((mk_circle_iff U r u v).mp hr |>.and hno)))))).exists
  have hroot (z : ℂ) (hz : z∈S i) : (z-u i)*(star z-v i)=1 := by
    have hh := congrArg (fun q : ℂ[X][X] => q.eval₂ (evalRingHom z) (star z)) hei
    simp only [circle,eval₂_sub,eval₂_mul,eval₂_C,coe_evalRingHom,eval_X,eval_C,
      eval₂_X,eval₂_one,hzi z hz,zero_mul] at hh
    exact sub_eq_zero.mp hh
  have hv := ComplexCircle.centers_conjugate (S i) (u i) (v i) (Nat.cast_lt.mp hci) hroot
  have hmem : S i⊆(P i).filter (fun z => ‖z-u i‖=1) := by
    intro z hzs
    refine Finset.mem_filter.mpr ⟨hsub i hzs,?_⟩
    apply (real_circle_iff z (u i)).mp
    rw [← hv]
    exact hroot z hzs
  apply hni (u i)
  · apply (show t i^((9:ℝ)/10)≤((S i).card : ℝ) by convert hfi using 1; norm_num).trans
    exact_mod_cast Finset.card_le_card hmem
  · constructor
    · exact (real_circle_iff _ _).mp (hv ▸ hpi)
    · exact (real_circle_iff _ _).mp (hv ▸ hri)
end PlanarUnitDistances.UltraCircle

end OAI
