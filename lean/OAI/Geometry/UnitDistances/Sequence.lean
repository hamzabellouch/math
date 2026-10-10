import OAI.Geometry.UnitDistances.Entropy

namespace OAI

namespace PlanarUnitDistances.IncidenceSequence
open Filter PowerGrowth CircleIncidence
open scoped Classical
noncomputable section
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def information (P Q : Finset Plane) : ℝ :=
  FiniteInformation.KL (IncidenceEntropy.wedge (GeometricLaw.E P Q))
    (fun pr => IncidenceEntropy.pointLaw (GeometricLaw.E P Q) pr.1*
      IncidenceEntropy.pointLaw (GeometricLaw.E P Q) pr.2)

lemma information_bound (P Q : Finset Plane) (he : 0 < incidences P Q)
    {d : ℝ} (hd : 0 < d) (hdeg : ∀q∈Q,d ≤ degree P q) :
    information P Q  ≤  2*Real.log (P.card:ℝ)-(1-(Q.card:ℝ)/incidences P Q)*
      Real.log (incidences P Q*d/2) := by
  have : Nonempty P := (Finset.card_pos.mp (GeometricLaw.card_pos P Q he).1).to_subtype
  have hge : 0 < IncidenceEntropy.edgeCount (GeometricLaw.E P Q) := by
    rw [GeometricLaw.edgeCount_eq]; exact he
  have hh := IncidenceEntropy.planar_wedge_information (GeometricLaw.E P Q)
    (fun p => (p:Plane)) (fun q => (q:Plane)) Subtype.val_injective Subtype.val_injective
    (fun _ _ h => h) hge hd (fun q => by rw [GeometricLaw.degree_eq]; exact hdeg q q.property)
  simpa only [information,Fintype.card_coe,GeometricLaw.edgeCount_eq] using hh

structure Good (t δ R : ℝ) (P Q : Finset Plane) (ξ : ℝ) : Prop where
  algebraicP : ∀p∈P,∀k,IsAlgebraic ℚ (p k)
  algebraicQ : ∀q∈Q,∀k,IsAlgebraic ℚ (q k)
  positive : 0 < incidences P Q
  error_nonneg : 0 ≤ ξ
  error_le : ξ ≤ δ
  expansion : ∀A ⊆ P,∀B ⊆ Q,incidences A B/incidences P Q  ≤
    Real.sqrt ((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))*
      (((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))^(1/25:ℝ)+ξ)
  atomP : ∀p∈P,(27/50:ℝ)/(P.card:ℝ) ≤ degree Q p/incidences P Q
  atomQ : ∀q∈Q,(27/50:ℝ)/(Q.card:ℝ) ≤ degree P q/incidences P Q
  cardP : (P.card:ℝ) ≤ t^(1+δ)
  atomUpper : ∀p∈P,degree Q p/incidences P Q ≤ t^(-1/2:ℝ)
  degreeP : t^(1/2:ℝ) ≤ (27/50:ℝ)*incidences P Q/P.card
  degreeQ : R ≤ (27/50:ℝ)*incidences P Q/Q.card
  wedgeBound : t^(2-δ) ≤ incidences P Q*((27/50:ℝ)*incidences P Q/Q.card)/2
  info : information P Q/Real.log t ≤ δ

theorem fixed_accuracy {t : ℕ → ℝ} {X : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1 ≤ t i) (hX0 : ∀i,(X i).Nonempty)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hE : Lower atTop t (fun i => incidences (X i) (X i)) 4)
    (hAlg : ∀i,∀p∈X i,∀k,IsAlgebraic ℚ (p k))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R : ℝ) :
    ∃P Q : ℕ → Finset Plane,∃ξ : ℕ → ℝ,
      ∀ᶠi in atTop,Good (t i) δ R (P i) (Q i) (ξ i) := by
  let a := δ/100
  let b := a/2000
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b < a/1000 := by dsimp [b]; linarith
  obtain ⟨P,Q,hPQ,hP,hQ,hE'⟩ := CuttingAsymptotics.exists_cut_sequence X ht ht1 hX0 hX hE ha ha1
  obtain ⟨F,G,hFG,hdF,hdG,hF,hG,hFG'⟩ := CuttingAsymptotics.trim_sequence ht ht1 hX
    (fun i => (hPQ i).1) (fun i => (hPQ i).2) ha ha1 hb (by linarith) hP hQ hE'
  obtain ⟨A,B,ξ,hξ,hA,hB,_,_,hAB,hd⟩ := RegularizedPiece.regularize ht ht1 hX
    (fun i => ((hFG i).1).trans (hPQ i).1) (fun i => ((hFG i).2).trans (hPQ i).2)
    ha ha1 hb hba hF hG hFG' hdF hdG
  let e := fun i => incidences (A i) (B i)
  let m := fun i => ((A i).card:ℝ)
  let n := fun i => ((B i).card:ℝ)
  have he0 := hAB.eventually_pos ht
  have hm0 : ∀ᶠi in atTop,(0:ℝ)  <  m i := by
    filter_upwards [he0] with i hi
    change (0:ℝ) < ((A i).card:ℝ)
    exact_mod_cast (GeometricLaw.card_pos (A i) (B i) hi).1
  have hn0 : ∀ᶠi in atTop,(0:ℝ)  <  n i := by
    filter_upwards [he0] with i hi
    change (0:ℝ) < ((B i).card:ℝ)
    exact_mod_cast (GeometricLaw.card_pos (A i) (B i) hi).2
  have hdp : Lower atTop t (fun i => (27/50:ℝ)*e i/m i) (1-5*b) := by
    have h := (hAB.div hA hm0 ht).const_mul ht (by norm_num : (0:ℝ) < 27/50)
    convert h using 1
    · ext i; dsimp only [e,m]; ring
    · ring
  have hdq : Lower atTop t (fun i => (27/50:ℝ)*e i/n i) (a-5*b) := by
    have h := (hAB.div hB hn0 ht).const_mul ht (by norm_num : (0:ℝ) < 27/50)
    convert h using 1
    · ext i; dsimp only [e,n]; ring
    · ring
  have hpup : Upper atTop t (fun i => (t i)^(1+b)/e i) (-1-2*a+6*b) := by
    have h := (upper_rpow ht (1+b)).div hAB he0 ht
    convert h using 1; ring
  have hprod : Lower atTop t (fun i => e i*((27/50:ℝ)*e i/n i)/2) (2+3*a-10*b) := by
    have h := (hAB.mul hdq ht).const_mul ht (by norm_num : (0:ℝ) < 1/2)
    convert h using 1
    · ext i; dsimp only [e]; ring
    · ring
  have hinfo := InformationPowers.information_rate (D := fun i => information (A i) (B i)) ht (by norm_num : (0:ℝ) < 27/50)
    hA hB hAB hm0 hn0 (by dsimp [b] at *; linarith : 2+a < 2+2*a-5*b)
    (by dsimp [b] at *; linarith : 0 < 2*(2+2*a-5*b)-(2+a))
  have hinfo' : ∀ᶠi in atTop,information (A i) (B i)/Real.log (t i) ≤ δ := by
    have hbound : ∀ᶠi in atTop,information (A i) (B i) ≤ 2*Real.log (m i)-
        (1-n i/e i)*Real.log (e i*((27/50:ℝ)*e i/n i)/2) := by
      filter_upwards [hd,he0,hn0] with i hi hei hni
      apply information_bound (A i) (B i) hei (by dsimp [e,n]; positivity)
      intro q hq
      have hh := hi.2.2.2.2.2.2 q hq
      have h := (le_div_iff₀ hei).mp hh
      simpa only [div_mul_eq_mul_div] using h
    have hh := hinfo hbound (δ-(a+10*b)) (by dsimp [a,b]; linarith)
    filter_upwards [hh] with i hi
    convert hi using 1; ring
  have had : 1+2*a < 1+δ := by dsimp [a]; linarith
  have hpd : (1/2:ℝ) < 1-5*b := by dsimp [b,a]; linarith
  have hqd : 0 < a-5*b := by dsimp [b]; linarith
  have hpud : -1-2*a+6*b < (-1/2:ℝ) := by dsimp [b]; linarith
  have hw : 2-δ < 2+3*a-10*b := by dsimp [b]; linarith
  refine ⟨A,B,ξ,?_⟩
  filter_upwards [hd,hξ.eventually_le_const hδ,hA.power_bound had,hdp.power_bound hpd,
    (hdq.tends_to_infinity ht hqd).eventually_ge_atTop R,hpup.power_bound hpud,
    hprod.power_bound hw,hinfo'] with i hi hξi hAi hdpi hdqi hpui hwi hIi
  rcases hi with ⟨hAi',hBi',hξ0,hei,hexp,hatP,hatQ⟩
  refine ⟨fun p hp => hAlg i p ((hPQ i).1 ((hFG i).1 (hAi' hp))),
    fun q hq => hAlg i q ((hPQ i).2 ((hFG i).2 (hBi' hq))),hei,hξ0,hξi,hexp,
    hatP,hatQ,hAi,?_,hdpi,hdqi,hwi,hIi⟩
  intro p hp
  apply (div_le_div_of_nonneg_right ?_ hei.le).trans hpui
  exact (CircleIncidence.degree_mono hBi' p).trans (hdF i p (hAi' hp))
lemma Good.point_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (p : P) : 0 < degree Q p := by
  have hm : (0:ℝ) < P.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).1
  have hh := (le_div_iff₀ h.positive).mp (h.atomP p p.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hm) h.positive).trans_le hh

lemma Good.center_degree_pos {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) (q : Q) : 0 < degree P q := by
  have hn : (0:ℝ) < Q.card := by exact_mod_cast (GeometricLaw.card_pos P Q h.positive).2
  have hh := (le_div_iff₀ h.positive).mp (h.atomQ q q.property)
  exact (mul_pos (div_pos (by norm_num : (0:ℝ) < 27/50) hn) h.positive).trans_le hh

lemma Good.information_nonneg {t δ R ξ : ℝ} {P Q : Finset Plane}
    (h : Good t δ R P Q ξ) : 0 ≤ information P Q := by
  have he : IncidenceEntropy.edgeCount (GeometricLaw.E P Q) ≠ 0 := by
    rw [GeometricLaw.edgeCount_eq]; exact h.positive.ne'
  have hd : ∀q : Q,IncidenceEntropy.degree (GeometricLaw.E P Q) q ≠ 0 := by
    intro q; rw [GeometricLaw.degree_eq]; exact (h.center_degree_pos q).ne'
  have hp : ∀p : P,0 < IncidenceEntropy.pointLaw (GeometricLaw.E P Q) p := by
    intro p
    rw [IncidenceEntropy.pointLaw,GeometricLaw.row_count,GeometricLaw.edgeCount_eq]
    exact div_pos (h.point_degree_pos p) h.positive
  exact FiniteInformation.KL_nonneg _ _ (IncidenceEntropy.wedge_nonneg _)
    (fun pr => (mul_pos (hp pr.1) (hp pr.2)).le) (IncidenceEntropy.wedge_sum _ he hd)
    (by rw [Fintype.sum_prod_type,←Finset.sum_mul_sum,IncidenceEntropy.pointLaw_sum _ he,one_mul])
    (fun pr _ => (mul_pos (hp pr.1) (hp pr.2)).ne')

structure Sequence where
  t : ℕ → ℝ
  P : ℕ → Finset Plane
  Q : ℕ → Finset Plane
  ξ : ℕ → ℝ
  large : ∀i : ℕ,(i:ℝ)+2 ≤ t i
  good : ∀i : ℕ,Good (t i) (1/((i:ℝ)+1)) ((i:ℝ)+1) (P i) (Q i) (ξ i)

lemma Sequence.tendsto (s : Sequence) : Tendsto s.t atTop atTop :=
  tendsto_atTop_mono (fun i => (by linarith [s.large i] : (i:ℝ) ≤ s.t i))
    tendsto_natCast_atTop_atTop

lemma Sequence.accuracy_limit : Tendsto (fun i : ℕ => 1/((i:ℝ)+1)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

lemma Sequence.error_limit (s : Sequence) : Tendsto s.ξ atTop (nhds 0) :=
  squeeze_zero (fun i => (s.good i).error_nonneg) (fun i => (s.good i).error_le)
    Sequence.accuracy_limit

lemma Sequence.information_limit (s : Sequence) :
    Tendsto (fun i => information (s.P i) (s.Q i)/Real.log (s.t i)) atTop (nhds 0) := by
  apply squeeze_zero (fun i => div_nonneg (s.good i).information_nonneg
    (Real.log_nonneg (by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i])))
    (fun i => (s.good i).info) Sequence.accuracy_limit

lemma Sequence.cardP_power (s : Sequence) : Upper atTop s.t (fun i => ((s.P i).card:ℝ)) 1 := by
  intro ε hε
  filter_upwards [Sequence.accuracy_limit.eventually_le_const hε] with i hi
  exact (s.good i).cardP.trans (Real.rpow_le_rpow_of_exponent_le
    (by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]) (by linarith))

lemma Sequence.wedge_power (s : Sequence) : Lower atTop s.t
    (fun i => incidences (s.P i) (s.Q i)*((27/50:ℝ)*incidences (s.P i) (s.Q i)/(s.Q i).card)/2) 2 := by
  intro ε hε
  filter_upwards [Sequence.accuracy_limit.eventually_le_const hε] with i hi
  exact (Real.rpow_le_rpow_of_exponent_le
    (by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]) (by linarith)).trans (s.good i).wedgeBound

theorem diagonal_sequence {t : ℕ → ℝ} {X : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1 ≤ t i) (hX0 : ∀i,(X i).Nonempty)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hE : Lower atTop t (fun i => incidences (X i) (X i)) 4)
    (hAlg : ∀i,∀p∈X i,∀k,IsAlgebraic ℚ (p k)) : Nonempty Sequence := by
  have hg (k : ℕ) := fixed_accuracy ht ht1 hX0 hX hE hAlg
    (δ := 1/((k:ℝ)+1)) (by positivity) (by
      apply (div_le_one (by positivity : (0:ℝ) < (k:ℝ)+1)).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) k]) ((k:ℝ)+1)
  choose P Q ξ hg using hg
  have hh (k : ℕ) : ∀ᶠi in atTop,Good (t i) (1/((k:ℝ)+1)) ((k:ℝ)+1)
      (P k i) (Q k i) (ξ k i) ∧ (k:ℝ)+2 ≤ t i :=
    (hg k).and (ht.eventually_ge_atTop ((k:ℝ)+2))
  obtain ⟨f,_,hf⟩ := PowerGrowth.diagonal hh
  exact ⟨⟨fun i => t (f i),fun i => P i (f i),fun i => Q i (f i),fun i => ξ i (f i),
    fun i => (hf i).2,fun i => (hf i).1⟩⟩

end
end PlanarUnitDistances.IncidenceSequence

namespace PlanarUnitDistances.CommonField
open Polynomial

theorem exists_normal_field (S : Finset ℂ) (halg : ∀ z∈S, IsAlgebraic ℚ z) :
    ∃ F : IntermediateField ℚ ℂ, (∀ z∈S,z∈F) ∧ FiniteDimensional ℚ F ∧ Normal ℚ F := by
  classical
  let A := IntermediateField.adjoin ℚ (S : Set ℂ)
  let : FiniteDimensional ℚ A := IntermediateField.finiteDimensional_adjoin
    (fun z hz => (halg z hz).isIntegral)
  let F := IntermediateField.normalClosure ℚ A ℂ
  let : IsNormalClosure ℚ A F := Algebra.IsAlgebraic.isNormalClosure_normalClosure
    (fun _ => IsAlgClosed.splits _)
  let : Normal ℚ F := IsNormalClosure.normal (F := ℚ) (K := A) (L := F)
  refine ⟨F,?_,inferInstance,inferInstance⟩
  intro z hz
  exact (A.val.fieldRange_le_normalClosure (K := A))
    ⟨⟨z,IntermediateField.subset_adjoin ℚ _ hz⟩,rfl⟩

lemma integral_I : IsIntegral ℚ Complex.I := by
  refine ⟨X^2+1,?_,?_⟩
  · exact monic_X_pow_add_C 1 (by decide : 2 ≠ 0)
  · simp

lemma algebraic_ofReal {x : ℝ} (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ (x : ℂ) :=
  (hx.isIntegral.map (IsScalarTower.toAlgHom ℚ ℝ ℂ)).isAlgebraic

lemma algebraic_coordinates (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i,IsAlgebraic ℚ (x i)) :
    IsAlgebraic ℚ ((x 0 : ℂ)+(x 1 : ℂ)*Complex.I) ∧
    IsAlgebraic ℚ ((x 0 : ℂ)-(x 1 : ℂ)*Complex.I) := by
  have h0 := (algebraic_ofReal (hx 0)).isIntegral
  have h1 := (algebraic_ofReal (hx 1)).isIntegral
  exact ⟨(h0.add (h1.mul integral_I)).isAlgebraic,(h0.sub (h1.mul integral_I)).isAlgebraic⟩
end PlanarUnitDistances.CommonField

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
abbrev Plane := EuclideanSpace ℝ (Fin 2)
variable (P Q : Finset Plane)
def location : P ⊕ Q → Plane := Sum.elim Subtype.val Subtype.val

structure Model where
  field : IntermediateField ℚ ℂ
  finite : FiniteDimensional ℚ field
  normal : Normal ℚ field
  z : P ⊕ Q → field
  w : P ⊕ Q → field
  z_eq : ∀v,(z v:ℂ)=UnitCodegree.zCoordinate (location P Q v)
  w_eq : ∀v,(w v:ℂ)=star (UnitCodegree.zCoordinate (location P Q v))

variable {P Q}
instance (M : Model P Q) : FiniteDimensional ℚ M.field := M.finite
instance (M : Model P Q) : Normal ℚ M.field := M.normal
instance (M : Model P Q) : NumberField M.field := ⟨⟩
instance (M : Model P Q) : IsGalois ℚ M.field := ⟨⟩

theorem exists_model
    (hP : ∀p∈P,∀i,IsAlgebraic ℚ (p i))
    (hQ : ∀q∈Q,∀i,IsAlgebraic ℚ (q i)) : Nonempty (Model P Q) := by
  let Z := fun v : P⊕Q => UnitCodegree.zCoordinate (location P Q v)
  let W := fun v : P⊕Q => star (Z v)
  have ha (v : P⊕Q) : IsAlgebraic ℚ (Z v) ∧ IsAlgebraic ℚ (W v) := by
    have h : ∀i,IsAlgebraic ℚ (location P Q v i) := by
      cases v with
      | inl p => exact hP p p.property
      | inr q => exact hQ q q.property
    have hh := CommonField.algebraic_coordinates (location P Q v) h
    constructor
    · exact hh.1
    · convert hh.2 using 1
      simp [W,Z,UnitCodegree.zCoordinate_apply,sub_eq_add_neg]
  let S : Finset ℂ := Finset.univ.image Z ∪ Finset.univ.image W
  have halg : ∀z∈S,IsAlgebraic ℚ z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact (ha v).1
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact (ha v).2
  obtain ⟨F,hF,hfin,hnorm⟩ := CommonField.exists_normal_field S halg
  refine ⟨⟨F,hfin,hnorm,fun v => ⟨Z v,hF _ ?_⟩,fun v => ⟨W v,hF _ ?_⟩,
    fun _ => rfl,fun _ => rfl⟩⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)

namespace Model
variable (M : Model P Q)
lemma point_injective : Function.Injective (M.z ∘ Sum.inl) := by
  intro p r h
  apply Subtype.val_injective
  apply UnitCodegree.zCoordinate.injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inl] using hh
lemma center_injective : Function.Injective (M.z ∘ Sum.inr) := by
  intro q r h
  apply Subtype.val_injective
  apply UnitCodegree.zCoordinate.injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inr] using hh
lemma unit_identity (p : P) (q : Q) (h : dist (p:Plane) (q:Plane)=1) :
    (M.z (.inl p)-M.z (.inr q))*(M.w (.inl p)-M.w (.inr q))=1 := by
  apply Subtype.val_injective
  change ((M.z (.inl p):ℂ)-(M.z (.inr q):ℂ))*((M.w (.inl p):ℂ)-(M.w (.inr q):ℂ))=1
  simp only [M.z_eq,M.w_eq,location,Sum.elim_inl,Sum.elim_inr]
  exact UnitCodegree.unit_distance_equation _ _ (by
    rw [UnitCodegree.zCoordinate.dist_map,dist_comm]; exact h)

lemma wpoint_injective : Function.Injective (M.w ∘ Sum.inl) := by
  intro p r h
  apply M.point_injective
  apply Subtype.val_injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simp only [Function.comp_apply,M.w_eq,location,Sum.elim_inl] at hh
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inl] using star_injective hh
lemma wcenter_injective : Function.Injective (M.w ∘ Sum.inr) := by
  intro p r h
  apply M.center_injective
  apply Subtype.val_injective
  have hh := congrArg (fun x : M.field => (x:ℂ)) h
  simp only [Function.comp_apply,M.w_eq,location,Sum.elim_inr] at hh
  simpa only [Function.comp_apply,M.z_eq,location,Sum.elim_inr] using star_injective hh

def support : Finset M.field :=
  (Finset.univ.image (fun vr : (P⊕Q)×(P⊕Q) => M.z vr.1-M.z vr.2) ∪
  Finset.univ.image (fun vr : (P⊕Q)×(P⊕Q) => M.w vr.1-M.w vr.2)) ∪
  Finset.univ.image (fun vrs : (P⊕Q)×(P⊕Q)×(P⊕Q) =>
    ((M.z vrs.1-M.z vrs.2.1)-(M.z vrs.1-M.z vrs.2.2))*
    ((M.z vrs.1-M.z vrs.2.1)⁻¹-(M.z vrs.1-M.z vrs.2.2)⁻¹))
lemma sub_mem (v r : P⊕Q) : M.z v-M.z r ∈ M.support :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(v,r),Finset.mem_univ _,rfl⟩))
lemma wsub_mem (v r : P⊕Q) : M.w v-M.w r ∈ M.support :=
  Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨(v,r),Finset.mem_univ _,rfl⟩))
lemma difference_mem (v r s : P⊕Q) :
    ((M.z v-M.z r)-(M.z v-M.z s))*((M.z v-M.z r)⁻¹-(M.z v-M.z s)⁻¹) ∈ M.support :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v,r,s),Finset.mem_univ _,rfl⟩)
end Model
end
end PlanarUnitDistances.CommonFieldModel

namespace PlanarUnitDistances.ExpansionConsequences
open Finset Real

noncomputable def mass {A : Type*} (μ : A → ℝ) (s : Finset A) : ℝ := ∑ a ∈ s, μ a
noncomputable def rect {P Q : Type*} (w : P → Q → ℝ)
    (F : Finset P) (G : Finset Q) : ℝ := ∑ p ∈ F, ∑ q ∈ G, w p q

section FiniteLaw
variable {P Q : Type*} [Fintype P] [Fintype Q]
variable (w : P → Q → ℝ)
noncomputable def left (p : P) : ℝ := ∑ q, w p q
noncomputable def right (q : Q) : ℝ := ∑ p, w p q
noncomputable def conditional (F : Finset P) (q : Q) : ℝ :=
  (∑ p ∈ F, w p q) / right w q

omit [Fintype P] in
lemma left_nonneg (hw : ∀ p q, 0 ≤ w p q) (p : P) : 0 ≤ left w p :=
  sum_nonneg (fun q _ => hw p q)
omit [Fintype Q] in
lemma right_nonneg (hw : ∀ p q, 0 ≤ w p q) (q : Q) : 0 ≤ right w q :=
  sum_nonneg (fun p _ => hw p q)
lemma mass_nonneg {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (s : Finset A) :
    0 ≤ mass μ s := sum_nonneg (fun a _ => hμ a)
lemma mass_le_one {A : Type*} [Fintype A] (μ : A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμsum : ∑ a, μ a = 1) (s : Finset A) :
    mass μ s ≤ 1 := by
  simpa [mass, hμsum] using
    sum_le_sum_of_subset_of_nonneg (subset_univ s) (fun a _ _ => hμ a)
lemma mass_mono {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {s t : Finset A} (hst : s ⊆ t) : mass μ s ≤ mass μ t :=
  sum_le_sum_of_subset_of_nonneg hst (fun a _ _ => hμ a)
lemma right_sum (hs : ∑ p, ∑ q, w p q = 1) : ∑ q, right w q = 1 := by
  unfold right
  rw [sum_comm]
  exact hs
omit [Fintype P] [Fintype Q] in
lemma rectangle_right (F : Finset P) (G : Finset Q) :
    rect w F G = ∑ q ∈ G, ∑ p ∈ F, w p q := by
  exact sum_comm
omit [Fintype Q] in
lemma conditional_nonneg (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (q : Q) :
    0 ≤ conditional w F q :=
  div_nonneg (sum_nonneg (fun p _ => hw p q)) (right_nonneg w hw q)
omit [Fintype Q] in
lemma conditional_le_one (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (q : Q) :
    conditional w F q ≤ 1 := by
  have hsub : (∑ p ∈ F, w p q) ≤ right w q :=
    sum_le_sum_of_subset_of_nonneg (subset_univ F) (fun p _ _ => hw p q)
  exact div_le_one_of_le₀ hsub (right_nonneg w hw q)
omit [Fintype Q] in
lemma right_mul_conditional (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (q : Q) :
    right w q * conditional w F q = ∑ p ∈ F, w p q := by
  have hsub : (∑ p ∈ F, w p q) ≤ right w q :=
    sum_le_sum_of_subset_of_nonneg (subset_univ F) (fun p _ _ => hw p q)
  by_cases hq : right w q = 0
  · have hz : (∑ p ∈ F, w p q) = 0 :=
      le_antisymm (hq ▸ hsub) (sum_nonneg (fun p _ => hw p q))
    simp [hq, hz]
  · exact mul_div_cancel₀ _ hq
lemma conditional_mean (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) :
    ∑ q, right w q * conditional w F q = mass (left w) F := by
  simp_rw [right_mul_conditional w hw]
  rw [sum_comm]
  rfl
omit [Fintype Q] in
lemma rectangle_conditional (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) (G : Finset Q) :
    rect w F G = ∑ q ∈ G, right w q * conditional w F q := by
  rw [rectangle_right]
  simp_rw [right_mul_conditional w hw]

lemma threshold_markov {Q : Type*} [Fintype Q] (κ g : Q → ℝ)
    (hκ : ∀ q, 0 ≤ κ q) (hg : ∀ q, 0 ≤ g q) {d : ℝ} (_hd : 0 ≤ d) :
    d * mass κ (univ.filter (fun q => d < g q)) ≤ ∑ q, κ q * g q := by
  classical
  rw [mass, mul_sum]
  calc
    _ ≤ ∑ q ∈ univ.filter (fun q => d < g q), κ q * g q := by
      apply sum_le_sum
      intro q hq
      calc
        d * κ q = κ q * d := mul_comm _ _
        _ ≤ κ q * g q := mul_le_mul_of_nonneg_left (le_of_lt (mem_filter.mp hq).2) (hκ q)
    _ ≤ ∑ q, κ q * g q :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => mul_nonneg (hκ q) (hg q))

noncomputable def wedgeMass (F : Finset P) : ℝ :=
  ∑ q, right w q * (conditional w F q)^2

lemma wedge_split (hw : ∀ p q, 0 ≤ w p q) (F : Finset P) {d : ℝ} (hd : 0 ≤ d) :
    wedgeMass w F ≤ d * mass (left w) F +
      rect w F (univ.filter (fun q => d < conditional w F q)) := by
  classical
  rw [← conditional_mean w hw, rectangle_conditional w hw, mul_sum,
    sum_filter, ← sum_add_distrib]
  unfold wedgeMass
  apply sum_le_sum
  intro q _
  have hk := right_nonneg w hw q
  have hg := conditional_nonneg w hw F q
  have hg1 := conditional_le_one w hw F q
  by_cases hq : d < conditional w F q
  · simp only [hq, ↓reduceIte]
    nlinarith [mul_nonneg hk (mul_nonneg hd hg),
      mul_nonneg hk (mul_nonneg hg (sub_nonneg.mpr hg1))]
  · simp only [hq, ↓reduceIte, add_zero]
    have hqd := le_of_not_gt hq
    nlinarith [mul_nonneg hk (mul_nonneg hg (sub_nonneg.mpr hqd))]

theorem wedge_rare (hw : ∀ p q, 0 ≤ w p q) (F : Finset P)
    {θ d : ℝ} (hθ : 0 ≤ θ) (hd : 0 < d)
    (hexp : ∀ G : Finset Q, rect w F G ≤
      θ * sqrt (mass (left w) F * mass (right w) G)) :
    wedgeMass w F ≤ (d + θ / sqrt d) * mass (left w) F := by
  classical
  let G : Finset Q := univ.filter (fun q => d < conditional w F q)
  let h := mass (left w) F
  let k := mass (right w) G
  have hh : 0 ≤ h := mass_nonneg _ (left_nonneg w hw) F
  have hk : 0 ≤ k := mass_nonneg _ (right_nonneg w hw) G
  have hdg : d*k ≤ h := by
    simpa [G, h, k, conditional_mean w hw] using
      threshold_markov (right w) (conditional w F) (right_nonneg w hw)
        (conditional_nonneg w hw F) hd.le
  have hroot : sqrt d * sqrt (h*k) ≤ h := by
    have hs := sq_sqrt (mul_nonneg hh hk)
    have hd2 := sq_sqrt hd.le
    have hn := sqrt_nonneg d
    have hn' := sqrt_nonneg (h*k)
    have hm := mul_le_mul_of_nonneg_left hdg hh
    nlinarith [sq_nonneg (sqrt d * sqrt (h*k) - h)]
  have hspos : 0 < sqrt d := sqrt_pos.mpr hd
  have hb : sqrt (h*k) ≤ h / sqrt d := (le_div_iff₀ hspos).mpr (by nlinarith)
  calc
    wedgeMass w F ≤ d*h + rect w F G := wedge_split w hw F hd.le
    _ ≤ d*h + θ*sqrt (h*k) := by linarith [hexp G]
    _ ≤ d*h + θ*(h / sqrt d) := by linarith [mul_le_mul_of_nonneg_left hb hθ]
    _ = (d + θ / sqrt d)*h := by ring

theorem one_small_set {h k δ C ξ η : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k)
    (hδ : h ≤ δ) (hk1 : k ≤ 1) (hC : 0 ≤ C) (hη : 0 ≤ η) :
    C * sqrt (h*k) * ((h*k)^η + ξ) ≤
      (C * (δ^η + ξ)) * sqrt (h*k) := by
  have hmul : h*k ≤ δ := (mul_le_of_le_one_right hh hk1).trans hδ
  have hp := rpow_le_rpow (mul_nonneg hh hk) hmul hη
  have := mul_le_mul_of_nonneg_left (add_le_add_right hp ξ)
    (mul_nonneg hC (sqrt_nonneg (h*k)))
  nlinarith

theorem height_tail_mass {A : Type*} [Fintype A] (μ a : A → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (ha : ∀ p, 0 ≤ a p)
    {C S R : ℝ} (hS : 0 < S) (hR : 0 < R)
    (hm : ∑ p, μ p * a p ≤ C*S) :
    mass μ (univ.filter (fun p => R*S < a p)) ≤ C/R := by
  classical
  have h := threshold_markov μ a hμ ha (mul_pos hR hS).le
  have hh : R * mass μ (univ.filter (fun p => R*S < a p)) ≤ C := by
    nlinarith
  exact (le_div_iff₀ hR).mpr (by nlinarith)
end FiniteLaw

section LabelMatching
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def mismatch (w : A → A → ℝ) : ℝ :=
  ∑ p, ∑ q, if p ≠ q then w p q else 0

def outside (a : A) : Finset A := univ.filter (fun p => p ≠ a)

lemma outside_mass (μ : A → ℝ) (hs : ∑ p, μ p = 1) (a : A) :
    mass μ (outside a) = 1 - μ a := by
  have he : outside a = univ.erase a := by ext p; simp [outside, ne_comm]
  rw [he, mass]
  have hh := sum_erase_add univ μ (mem_univ a)
  linarith

lemma matched_add_mismatch (w : A → A → ℝ) :
    (∑ a, w a a) + mismatch w = ∑ p, ∑ q, w p q := by
  have he (p : A) : w p p = ∑ q, if p = q then w p q else 0 := by simp
  simp_rw [he]
  unfold mismatch
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  by_cases h : p=q <;> simp [h]

lemma mass_left_indicator (w : A → A → ℝ) (a : A) :
    mass (left w) (outside a) = ∑ p, ∑ q, if p ≠ a then w p q else 0 := by
  simp only [mass, outside, sum_filter, left, sum_ite_irrel, sum_const_zero]
lemma mass_right_indicator (w : A → A → ℝ) (a : A) :
    mass (right w) (outside a) = ∑ p, ∑ q, if q ≠ a then w p q else 0 := by
  rw [sum_comm]
  simp only [mass, outside, sum_filter, right, sum_ite_irrel, sum_const_zero]
lemma rect_outside_indicator (w : A → A → ℝ) (a : A) :
    rect w (outside a) (outside a) =
      ∑ p, ∑ q, if p ≠ a ∧ q ≠ a then w p q else 0 := by
  simp only [rect, outside, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p ≠ a
  · simp [hp]
  · simp [hp]

lemma exactly_one_le_mismatch (w : A → A → ℝ) (hw : ∀ p q, 0 ≤ w p q) (a : A) :
    mass (left w) (outside a) + mass (right w) (outside a) ≤
      mismatch w + 2*rect w (outside a) (outside a) := by
  rw [mass_left_indicator, mass_right_indicator, rect_outside_indicator]
  unfold mismatch
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro q _
  by_cases hp : p=a <;> by_cases hq : q=a <;> by_cases he : p=q <;>
    simp_all <;> linarith [hw p q]

omit [DecidableEq A] in
lemma diagonal_expansion (w : A → A → ℝ) (U V : A → ℝ)
    (hU : ∀ a, 0 ≤ U a) (hV : ∀ a, 0 ≤ V a)
    (hUs : ∑ a, U a = 1) (hVs : ∑ a, V a = 1)
    {η ξ z : ℝ} (hη : 0 ≤ η) (hξ : 0 ≤ ξ) (hz : 0 ≤ z)
    (huv : ∀ a, U a * V a ≤ z)
    (hexp : ∀ a, w a a ≤ sqrt (U a*V a) * ((U a*V a)^η+ξ)) :
    ∑ a, w a a ≤ z^η+ξ := by
  have hcs : ∑ a, sqrt (U a*V a) ≤ 1 := by
    simpa only [sqrt_mul (hU _), hUs, hVs, sqrt_one, mul_one] using
      sum_sqrt_mul_sqrt_le univ hU hV
  calc
    _ ≤ ∑ a, sqrt (U a*V a) * (z^η+ξ) := by
      apply sum_le_sum
      intro a _
      exact (hexp a).trans (mul_le_mul_of_nonneg_left
        (by linarith [rpow_le_rpow (mul_nonneg (hU a) (hV a)) (huv a) hη])
        (sqrt_nonneg _))
    _ = (∑ a, sqrt (U a*V a)) * (z^η+ξ) := by rw [sum_mul]
    _ ≤ z^η+ξ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg (rpow_nonneg hz η) hξ)]

theorem matching_dominant (w : A → A → ℝ) (U V : A → ℝ)
    (hw : ∀ p q, 0 ≤ w p q) (hws : ∑ p, ∑ q, w p q = 1)
    (hU : ∀ a, 0 ≤ U a) (hV : ∀ a, 0 ≤ V a)
    (hUs : ∑ a, U a = 1) (hVs : ∑ a, V a = 1)
    {γ η ξ ε : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleft : ∀ a, γ*U a ≤ left w a) (hright : ∀ a, γ*V a ≤ right w a)
    (hexp : ∀ F G : Finset A, rect w F G ≤
      sqrt (mass U F * mass V G) * ((mass U F * mass V G)^η+ξ))
    (hsmall : (1-ε)^η+ξ < 1-mismatch w)
    (htiny : ε^η+ξ ≤ γ/2) :
    ∃ a, mass (left w) (outside a) + mass (right w) (outside a) ≤ 2*mismatch w := by
  have hUle (a : A) : U a ≤ 1 := by
    simpa [mass] using mass_le_one U hU hUs {a}
  have hVle (a : A) : V a ≤ 1 := by
    simpa [mass] using mass_le_one V hV hVs {a}
  have hex : ∃ a, 1-ε < U a * V a := by
    by_contra hn
    push Not at hn
    have he := diagonal_expansion w U V hU hV hUs hVs hη hξ (sub_nonneg.mpr hε1) hn
      (fun a => by simpa [rect, mass] using hexp {a} {a})
    have heq := matched_add_mismatch w
    linarith
  obtain ⟨a,ha⟩ := hex
  let F := outside a
  let h := mass (left w) F
  let k := mass (right w) F
  let x := mass U F
  let y := mass V F
  have hx0 : 0 ≤ x := mass_nonneg U hU F
  have hy0 : 0 ≤ y := mass_nonneg V hV F
  have hx : x ≤ ε := by
    have hp := mul_le_of_le_one_right (hU a) (hVle a)
    dsimp [x,F]
    rw [outside_mass U hUs]
    linarith
  have hy : y ≤ ε := by
    have hp := mul_le_of_le_one_left (hV a) (hUle a)
    dsimp [y,F]
    rw [outside_mass V hVs]
    linarith
  have hdL : γ*x ≤ h := by
    dsimp [x,h,mass]
    rw [mul_sum]
    exact sum_le_sum (fun a _ => hleft a)
  have hdR : γ*y ≤ k := by
    dsimp [y,k,mass]
    rw [mul_sum]
    exact sum_le_sum (fun a _ => hright a)
  have hsqrt : 2*γ*sqrt (x*y) ≤ h+k := by
    have hh := sq_sqrt (mul_nonneg hx0 hy0)
    have hr := sqrt_nonneg (x*y)
    have hs : 2*sqrt (x*y) ≤ x+y := by nlinarith [sq_nonneg (x-y)]
    have := mul_le_mul_of_nonneg_left hs hγ.le
    linarith
  have hxy : x*y ≤ ε := (mul_le_of_le_one_right hx0 (hy.trans hε1)).trans hx
  have hpow := rpow_le_rpow (mul_nonneg hx0 hy0) hxy hη
  have hJ : rect w F F ≤ (h+k)/4 := by
    have he := hexp F F
    have hm := mul_le_mul_of_nonneg_left (show (x*y)^η+ξ ≤ γ/2 by linarith)
      (sqrt_nonneg (x*y))
    change rect w F F ≤ sqrt (x*y) * ((x*y)^η+ξ) at he
    nlinarith
  refine ⟨a, ?_⟩
  have hm := exactly_one_le_mismatch w hw a
  change h+k ≤ 2*mismatch w
  change h+k ≤ mismatch w + 2*rect w F F at hm
  linarith

lemma independent_mismatch_le (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (hs : ∑ a, μ a = 1) (a : A) :
    mismatch (fun p q => μ p * μ q) ≤ 2*mass μ (outside a) := by
  have he : ∀ p q, (if p ≠ q then μ p*μ q else 0) ≤
      (if p ≠ a then μ p*μ q else 0) + (if q ≠ a then μ p*μ q else 0) := by
    intro p q
    by_cases hp : p=a <;> by_cases hq : q=a <;> by_cases he : p=q <;>
      simp_all <;> nlinarith [mul_nonneg (hμ p) (hμ q)]
  have hh := sum_le_sum (s := univ) (fun p _ => sum_le_sum (s := univ) (fun q _ => he p q))
  simp only [sum_add_distrib] at hh
  rw [← mass_left_indicator, ← mass_right_indicator] at hh
  have hl : left (fun p q => μ p*μ q) = μ := by
    funext p
    simp [left, ← mul_sum, hs]
  have hr : right (fun p q => μ p*μ q) = μ := by
    funext q
    simp [right, ← sum_mul, hs]
  rw [hl,hr] at hh
  unfold mismatch
  linarith

lemma mismatch_nonneg (w : A → A → ℝ) (hw : ∀ p q, 0 ≤ w p q) :
    0 ≤ mismatch w := by
  unfold mismatch
  exact sum_nonneg (fun p _ => sum_nonneg (fun q _ => by split_ifs; exact hw p q; exact le_rfl))
lemma mismatch_le_one (w : A → A → ℝ) (hw : ∀ p q, 0 ≤ w p q)
    (hws : ∑ p, ∑ q, w p q = 1) : mismatch w ≤ 1 := by
  rw [← hws]
  exact sum_le_sum (fun p _ => sum_le_sum (fun q _ => by split_ifs <;> simp_all))

end LabelMatching

theorem matching_parameters {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃ ε s₀ ξ₀ : ℝ, 0 < s₀ ∧ 0 < ξ₀ ∧ 0 ≤ ε ∧ ε ≤ 1 ∧
      ∀ s ξ : ℝ, ξ ≤ ξ₀ → s ≤ s₀ →
        (1-ε)^η+ξ < 1-s ∧ ε^η+ξ ≤ γ/2 := by
  let b := min (γ/4) (1/2 : ℝ)
  have hb : 0 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let ε := b^(1/η)
  have he0 : 0 < ε := rpow_pos_of_pos hb _
  have he1 : ε < 1 := rpow_lt_one hb.le hb1 (one_div_pos.mpr hη)
  have he : ε^η = b := by
    dsimp [ε]
    rw [← rpow_mul hb.le, one_div_mul_cancel hη.ne', rpow_one]
  have hg : 0 < 1-(1-ε)^η := by
    have := rpow_lt_one (by linarith : 0 ≤ 1-ε) (by linarith : 1-ε < 1) hη
    linarith
  let s₀ := (1-(1-ε)^η)/4
  let ξ₀ := min (γ/4) s₀
  refine ⟨ε,s₀,ξ₀,by dsimp [s₀]; positivity,lt_min (by linarith) (by dsimp [s₀]; positivity),
    he0.le,he1.le,?_⟩
  intro s ξ hξ hs
  have hξs : ξ ≤ s₀ := hξ.trans (min_le_right _ _)
  have hξγ : ξ ≤ γ/4 := hξ.trans (min_le_left _ _)
  have hbγ : b ≤ γ/4 := min_le_left _ _
  dsimp [s₀] at hs hξs
  constructor <;> linarith

universe u

theorem uniform_label_matching {γ η : ℝ} (hγ : 0 < γ) (hη : 0 < η) :
    ∃ s₀ ξ₀ C : ℝ, 0 < s₀ ∧ 0 < ξ₀ ∧ 0 < C ∧
    ∀ (A : Type u) [Fintype A] [DecidableEq A]
      (w : A → A → ℝ) (U V : A → ℝ),
      (∀ p q, 0 ≤ w p q) → (∑ p, ∑ q, w p q = 1) →
      (∀ a, 0 ≤ U a) → (∀ a, 0 ≤ V a) → (∑ a, U a = 1) → (∑ a, V a = 1) →
      (∀ a, γ*U a ≤ left w a) → (∀ a, γ*V a ≤ right w a) →
      ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ ξ₀ →
      (∀ F G : Finset A, rect w F G ≤
        sqrt (mass U F * mass V G) * ((mass U F * mass V G)^η+ξ)) →
      (mismatch w ≤ s₀ → ∃ a, mass (left w) (outside a) +
        mass (right w) (outside a) ≤ C*mismatch w) ∧
      mismatch (fun p q => left w p * left w q) ≤ C*mismatch w ∧
      mismatch (fun p q => right w p * right w q) ≤ C*mismatch w := by
  obtain ⟨ε,s₀,ξ₀,hs₀,hξ₀,he0,he1,hpar⟩ := matching_parameters hγ hη
  let C := max (4 : ℝ) (1/s₀)
  have hC4 : 4 ≤ C := le_max_left _ _
  have hCs : 1/s₀ ≤ C := le_max_right _ _
  refine ⟨s₀,ξ₀,C,hs₀,hξ₀,lt_of_lt_of_le (by norm_num : (0:ℝ)<4) hC4,?_⟩
  intro A _ _ w U V hw hws hU hV hUs hVs hl hr ξ hξ hξb hexp
  have hls : ∑ a, left w a = 1 := hws
  have hrs : ∑ a, right w a = 1 := right_sum w hws
  have hmn := mismatch_nonneg w hw
  have hmnL := left_nonneg w hw
  have hmnR := right_nonneg w hw
  have hsmall (hs : mismatch w ≤ s₀) : ∃ a, mass (left w) (outside a) +
      mass (right w) (outside a) ≤ 2*mismatch w := by
    obtain ⟨ha,hb⟩ := hpar (mismatch w) ξ hξb hs
    exact matching_dominant w U V hw hws hU hV hUs hVs hγ hη.le hξ he0 he1
      hl hr hexp ha hb
  have hindL : mismatch (fun p q => left w p*left w q) ≤ 1 := by
    apply mismatch_le_one _ (fun p q => mul_nonneg (hmnL p) (hmnL q))
    simp_rw [← mul_sum, hls, mul_one]
    exact hls
  have hindR : mismatch (fun p q => right w p*right w q) ≤ 1 := by
    apply mismatch_le_one _ (fun p q => mul_nonneg (hmnR p) (hmnR q))
    simp_rw [← mul_sum, hrs, mul_one]
    exact hrs
  constructor
  · intro hs
    obtain ⟨a,ha⟩ := hsmall hs
    exact ⟨a, ha.trans (mul_le_mul_of_nonneg_right (by linarith : 2 ≤ C) hmn)⟩
  by_cases hs : mismatch w ≤ s₀
  · obtain ⟨a,ha⟩ := hsmall hs
    have hl0 := mass_nonneg _ hmnL (outside a)
    have hr0 := mass_nonneg _ hmnR (outside a)
    have hlb := independent_mismatch_le (left w) hmnL hls a
    have hrb := independent_mismatch_le (right w) hmnR hrs a
    have hc := mul_le_mul_of_nonneg_right hC4 hmn
    constructor <;> linarith
  · have hbig : 1 ≤ C*mismatch w := by
      have hgt : s₀ ≤ mismatch w := le_of_lt (lt_of_not_ge hs)
      have hdiv : 1 ≤ mismatch w / s₀ := (le_div_iff₀ hs₀).mpr (by simpa)
      have hc := mul_le_mul_of_nonneg_right hCs hmn
      have hid : mismatch w / s₀ = (1/s₀)*mismatch w := by ring
      rw [hid] at hdiv
      exact hdiv.trans hc
    exact ⟨hindL.trans hbig, hindR.trans hbig⟩

end PlanarUnitDistances.ExpansionConsequences

namespace PlanarUnitDistances.LawExpansion
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q A : Type*} [Fintype P] [Fintype Q] [Fintype A]

lemma push_event {X Y : Type*} [Fintype X] [Fintype Y] (μ : Law X) (f : X → Y) (g : Y → Prop) :
    event (push μ f) g=event μ (fun x => g (f x)) := push_avg μ f _

lemma mass_event (μ : Law P) (F : Finset P) :
    ExpansionConsequences.mass μ.val F=event μ (fun p => p∈F) := by
  unfold ExpansionConsequences.mass event avg
  simp only [mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_of_subset (subset_univ _)]

lemma rect_event (π : Law (P×Q)) (F : Finset P) (G : Finset Q) :
    ExpansionConsequences.rect (fun p q => π.val (p,q)) F G=
      event π (fun pq => pq.1∈F ∧ pq.2∈G) := by
  simp only [ExpansionConsequences.rect,event,avg,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]
  symm
  calc
    _ = ∑p,if p∈F then ∑q∈G,π.val (p,q) else 0 := by
      apply sum_congr rfl
      intro p _
      by_cases hp : p∈F
      · simp only [hp,true_and,↓reduceIte,←sum_filter,filter_mem_eq_of_subset (subset_univ _)]
      · simp [hp]
    _ = _ := by rw [←sum_filter,filter_mem_eq_of_subset (subset_univ _)]

lemma left_val (π : Law (P×Q)) (p : P) :
    ExpansionConsequences.left (fun p q => π.val (p,q)) p=(FiniteStarCoupling.left π).val p := by
  simp only [ExpansionConsequences.left,FiniteStarCoupling.left,push,fiberMass_eq,Fintype.sum_prod_type]
  rw [sum_comm]
  simp
lemma right_val (π : Law (P×Q)) (q : Q) :
    ExpansionConsequences.right (fun p q => π.val (p,q)) q=(FiniteStarCoupling.right π).val q := by
  simp [ExpansionConsequences.right,FiniteStarCoupling.right,push,fiberMass_eq,Fintype.sum_prod_type]
lemma total (π : Law (P×Q)) : ∑p,∑q,π.val (p,q)=1 := by
  simpa only [Fintype.sum_prod_type] using π.total

lemma mismatch_event (π : Law (A×A)) :
    ExpansionConsequences.mismatch (fun a b => π.val (a,b))=event π (fun ab => ab.1≠ab.2) := by
  simp only [ExpansionConsequences.mismatch,event,avg,Fintype.sum_prod_type,mul_ite,mul_one,mul_zero]

lemma outside_event (μ : Law A) (a : A) :
    ExpansionConsequences.mass μ.val (ExpansionConsequences.outside a)=event μ (fun x => x≠a) := by
  rw [mass_event]
  simp only [ExpansionConsequences.outside,mem_filter,mem_univ,true_and]

lemma fiber_domination {X Y : Type*} [Fintype X] [Fintype Y] (μ ν : Law X) (f : X → Y)
    {γ : ℝ} (h : ∀x,γ*μ.val x≤ν.val x) (y : Y) : γ*(push μ f).val y≤(push ν f).val y := by
  simp only [push,fiberMass_eq,mul_sum]
  apply sum_le_sum
  intro x _
  split_ifs <;> simp_all

lemma pushed_left (π : Law (P×Q)) (a : P → A) (b : Q → A) (l : A) :
    (FiniteStarCoupling.left (push π (fun pq => (a pq.1,b pq.2)))).val l=
      (push (FiniteStarCoupling.left π) a).val l := by
  change event (push π (fun pq => (a pq.1,b pq.2))) (fun ab => ab.1=l)=event (push π Prod.fst) (fun p => a p=l)
  simp only [push_event]
lemma pushed_right (π : Law (P×Q)) (a : P → A) (b : Q → A) (l : A) :
    (FiniteStarCoupling.right (push π (fun pq => (a pq.1,b pq.2)))).val l=
      (push (FiniteStarCoupling.right π) b).val l := by
  change event (push π (fun pq => (a pq.1,b pq.2))) (fun ab => ab.2=l)=event (push π Prod.snd) (fun q => b q=l)
  simp only [push_event]

theorem matching {γ η : ℝ} (hγ : 0<γ) (hη : 0<η) :
    ∃ s₀ ξ₀ C : ℝ,0<s₀ ∧ 0<ξ₀ ∧ 0<C ∧
    ∀ (P Q A : Type) [Fintype P] [Fintype Q] [Fintype A],
    ∀(π : Law (P×Q)) (U : Law P) (W : Law Q) (a : P → A) (b : Q → A),
    (∀p,γ*U.val p≤(FiniteStarCoupling.left π).val p) →
    (∀q,γ*W.val q≤(FiniteStarCoupling.right π).val q) →
    ∀ξ : ℝ,0≤ξ → ξ≤ξ₀ →
    (∀F : Finset P,∀G : Finset Q,event π (fun pq => pq.1∈F ∧ pq.2∈G)≤
      Real.sqrt (event U (fun p => p∈F)*event W (fun q => q∈G))*
        ((event U (fun p => p∈F)*event W (fun q => q∈G))^η+ξ)) →
    (event π (fun pq => a pq.1≠b pq.2)≤ s₀ →
      ∃l,event (FiniteStarCoupling.left π) (fun p => a p≠l)+
        event (FiniteStarCoupling.right π) (fun q => b q≠l)≤C*event π (fun pq => a pq.1≠b pq.2)) := by
  obtain ⟨s₀,ξ₀,C,hs,hξ,hC,hmatch⟩ := ExpansionConsequences.uniform_label_matching hγ hη
  refine ⟨s₀,ξ₀,C,hs,hξ,hC,?_⟩
  intro P Q A _ _ _ π U W a b hl hr ξ hξ0 hξb hexp hm
  let σ := push π (fun pq => (a pq.1,b pq.2))
  have he (F G : Finset A) : ExpansionConsequences.rect (fun a b => σ.val (a,b)) F G ≤
      Real.sqrt (ExpansionConsequences.mass (push U a).val F*ExpansionConsequences.mass (push W b).val G)*
      ((ExpansionConsequences.mass (push U a).val F*ExpansionConsequences.mass (push W b).val G)^η+ξ) := by
    simp only [rect_event,mass_event,σ,push_event]
    simpa only [mem_filter,mem_univ,true_and] using hexp (univ.filter (fun p => a p∈F)) (univ.filter (fun q => b q∈G))
  have hb := (hmatch A (fun a b => σ.val (a,b)) (push U a).val (push W b).val
    (fun a b => σ.nonneg (a,b)) (total σ) (push U a).nonneg (push W b).nonneg
    (push U a).total (push W b).total
    (fun l => by rw [left_val,pushed_left]; exact fiber_domination U (FiniteStarCoupling.left π) a hl l)
    (fun l => by rw [right_val,pushed_right]; exact fiber_domination W (FiniteStarCoupling.right π) b hr l)
    ξ hξ0 hξb he).1
  have hm' : ExpansionConsequences.mismatch (fun a b => σ.val (a,b))≤ s₀ := by
    simpa only [mismatch_event,σ,push_event] using hm
  obtain ⟨l,hl⟩ := hb hm'
  refine ⟨l,?_⟩
  have hle : ExpansionConsequences.left (fun a b => σ.val (a,b))=(push (FiniteStarCoupling.left π) a).val := by
    funext l
    rw [left_val]
    exact pushed_left π a b l
  have hre : ExpansionConsequences.right (fun a b => σ.val (a,b))=(push (FiniteStarCoupling.right π) b).val := by
    funext l
    rw [right_val]
    exact pushed_right π a b l
  rw [hle,hre,outside_event,outside_event,push_event,push_event,mismatch_event] at hl
  simpa only [σ,push_event] using hl
end
end PlanarUnitDistances.LawExpansion

namespace PlanarUnitDistances.LabelFromMatching
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q A : Type} [Fintype P] [Fintype Q] [Fintype A]

omit [Fintype A] in
lemma pair_mismatch (μ : Law P) (a : P → A) (l : A) :
    event (pair μ μ) (fun pp => a pp.1 ≠ a pp.2)  ≤  2*event μ (fun p => a p ≠ l) := by
  classical
  calc
    _  ≤  event (pair μ μ) (fun pp => a pp.1 ≠ l ∨ a pp.2 ≠ l) :=
      event_mono _ (fun pp h => by by_contra hn; simp only [not_or,not_not] at hn; exact h (hn.1.trans hn.2.symm))
    _ ≤ _ := pair_union μ (fun p => a p ≠ l)

omit [Fintype A] in
lemma control {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (π : Law (P×Q)) (a : P → A) (b : Q → A)
    (hm : event π (fun pq => a pq.1 ≠ b pq.2) ≤ s →
      ∃l,event (left π) (fun p => a p ≠ l)+event (right π) (fun q => b q ≠ l) ≤ C*event π (fun pq => a pq.1 ≠ b pq.2)) :
    event (pair (left π) (left π)) (fun pp => a pp.1 ≠ a pp.2)  ≤
      (2*C+1/s)*event π (fun pq => a pq.1 ≠ b pq.2) := by
  have h0 := event_nonneg π (fun pq => a pq.1 ≠ b pq.2)
  by_cases h : event π (fun pq => a pq.1 ≠ b pq.2) ≤ s
  · obtain ⟨l,hl⟩ := hm h
    have hb := pair_mismatch (left π) a l
    have hz := event_nonneg (right π) (fun q => b q ≠ l)
    have hi : 0 ≤ (1/s)*event π (fun pq => a pq.1 ≠ b pq.2) := mul_nonneg (by positivity) h0
    nlinarith
  · have hb := event_le_one (pair (left π) (left π)) (fun pp => a pp.1 ≠ a pp.2)
    have hd : 1 ≤ (1/s)*event π (fun pq => a pq.1 ≠ b pq.2) := by rw [one_div,mul_comm,←div_eq_mul_inv]; exact (le_div_iff₀ hs).2 (by linarith)
    have hc : 0 ≤ 2*C*event π (fun pq => a pq.1 ≠ b pq.2) := by positivity
    nlinarith

end
end PlanarUnitDistances.LabelFromMatching

end OAI
