import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OrientedFiniteCost

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def threeOrientedFinitePredictor (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) :=
  orientedFinitePredictor (threeFinitePredictor hd σ U UT P τ R L₀)
    (threeFinitePredictor (Subspace.dual_finrank_eq.trans hd) σ UT
      (U.map bidualPoint.toEmbedding) P τ R L₀)
    U UT 4 (1000*(Nat.card K)^2) (Nat.card K) P (9/1000) 10

theorem eventually_three_finite_oriented {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=4) (S U : Finset (ℙ K V))
       (T UT : Finset (ℙ K (Dual K V))) (_hT : T.Nonempty),
      Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → S.Nonempty → S⊆U → T⊆UT →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^4*Real.exp (-b)≤(S.card:ℝ)*T.card →
        let pred := threeOrientedFinitePredictor hd σ U UT (P η σ D R) τ R L₀
        let p := pred.output S T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→CaptureBound S U (9/1000) ((S.card:ℝ)*Real.exp (10*P η σ D R)) W) ∧
        (∀t m,pred.encoded S T t=some m→pred.cost t m≤
          9000*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  have hsparse : ∀ᶠ σ : ℝ in atTop,σ^(-400*beta η)≤(9:ℝ)/1000000 := by
    have hp : 0<400*beta η := mul_pos (by norm_num) (beta_pos hη)
    exact (Filter.Eventually.mono ((tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<9/1000000))) fun σ h=>by simpa only [neg_mul] using h.le
  filter_upwards [eventually_three_finite_predictor hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb,hsparse,eventually_ge_atTop (1:ℝ)] with σ hbase hrev hsparse hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ _ hd S U T UT hT hcard hσq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have hτ200 := hτhi.trans (Real.rpow_le_rpow_of_exponent_le hσ
    (by have := beta_pos hη;linarith : -400*beta η≤-200*beta η))
  obtain ⟨hP,hbP,heP,_,hq3⟩ := hrev D R b τ hr hbhi hτ.le hτ200
  have hqnat : 3≤Nat.card K := by exact_mod_cast (hq ▸ hq3 : (3:ℝ)≤Nat.card K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  have hn := reverseLength_universal_bound σ hσ hq.symm (by omega : finrank K V≤5) S U hS hSU
  have hgeom :
      let p := (threeOrientedFinitePredictor hd σ U UT (P η σ D R) τ R L₀).output S T
      p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
      ∀W,0<p (some W)→CaptureBound S U (9/1000) ((S.card:ℝ)*Real.exp (10*P η σ D R)) W := by
    rw [threeOrientedFinitePredictor,orientedFinite_output _ _ S U T UT hT 4 _ _ _ _ _ (by norm_num) hn]
    split_ifs with hST
    · obtain ⟨hf,hg,_⟩ := hbase D b τ R L₀ q K V hd S U T UT hcard hσq hr hL hb hbhi hτ hτhi hSU hTU hST hdens hprod
      exact ⟨hf.trans (by nlinarith only [Real.exp_pos (-(Nat.card K:ℝ))]),hg⟩
    · have hddual : finrank K (Dual K V)=4 := Subspace.dual_finrank_eq.trans hd
      have hTS : T.card≤(S.map bidualPoint.toEmbedding).card := by rw [Finset.card_map];omega
      have hSU' : S.map bidualPoint.toEmbedding⊆U.map bidualPoint.toEmbedding := Finset.map_subset_map.mpr hSU
      have hdens' : (Nat.card K:ℝ)*(incidences T (S.map bidualPoint.toEmbedding):ℝ)≤
          τ*T.card*(S.map bidualPoint.toEmbedding).card := by
        rw [incidences_bidual,Finset.card_map]
        nlinarith only [hdens]
      have hprod' : (Nat.card K:ℝ)^4*Real.exp (-b)≤(T.card:ℝ)*(S.map bidualPoint.toEmbedding).card := by
        rw [Finset.card_map];nlinarith only [hprod]
      obtain ⟨hf,hg,_⟩ := hbase D b τ R L₀ q K (Dual K V) hddual T UT
        (S.map bidualPoint.toEmbedding) (U.map bidualPoint.toEmbedding)
        hcard hσq hr hL hb hbhi hτ hτhi hTU hSU' hTS hdens' hprod'
      have hsparse' : 1000*(Nat.card K:ℝ)*incidences S T≤(9:ℝ)/1000*S.card*T.card := by
        have htau := hτhi.trans hsparse
        have hh := mul_le_mul_of_nonneg_left hdens (by norm_num : (0:ℝ)≤1000)
        have hh' := mul_le_mul_of_nonneg_right htau (show (0:ℝ)≤(S.card:ℝ)*T.card from mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        nlinarith only [hh,hh']
      have hl := reverseLength_spec (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) hq1 (enclosure_gap_nonneg S U hS hSU)
      obtain ⟨hf',hg'⟩ := reverse_after_general_capture (d:=3) hd (by norm_num) hqnat S U hS hSU T UT hT
        (9/1000) (by norm_num) (by norm_num)
        ((T.card:ℝ)*Real.exp (10*P η σ D R)) (2*Real.exp (-(Nat.card K:ℝ)))
        ((threeFinitePredictor hddual σ UT (U.map bidualPoint.toEmbedding) (P η σ D R) τ R L₀).output T (S.map bidualPoint.toEmbedding))
        hf hg hsparse' (reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))) hl.1 hl.2.1
      refine ⟨by convert hf' using 1; ring,?_⟩
      intro W hW
      have hw := hg' W hW
      refine ⟨hw.1,hw.2.1.trans ?_,?_⟩
      · exact three_cap_size_absorb _ _ _ _ _ (Nat.cast_nonneg _) (by exact_mod_cast hT.card_pos) hprod (by linarith) hbP heP
      · exact (mul_le_mul_of_nonneg_right (by norm_num : (9/1000:ℝ)≤9/10) (Nat.cast_nonneg _)).trans hw.2.2
  refine ⟨hgeom.1,hgeom.2,?_⟩
  apply orientedFinite_cost _ _ σ hσ hq.symm (by omega : finrank K V≤5) S U hS hSU T UT hT hTU
    (P η σ D R) hP 4
  · intro hST
    exact (hbase D b τ R L₀ q K V hd S U T UT hcard hσq hr hL hb hbhi hτ hτhi hSU hTU hST hdens hprod).2.2
  · intro hTS t m hm
    have hddual : finrank K (Dual K V)=4 := Subspace.dual_finrank_eq.trans hd
    have hTS' : T.card≤(S.map bidualPoint.toEmbedding).card := by simpa using hTS
    have hSU' : S.map bidualPoint.toEmbedding⊆U.map bidualPoint.toEmbedding := Finset.map_subset_map.mpr hSU
    have hdens' : (Nat.card K:ℝ)*(incidences T (S.map bidualPoint.toEmbedding):ℝ)≤
        τ*T.card*(S.map bidualPoint.toEmbedding).card := by
      rw [incidences_bidual,Finset.card_map]
      nlinarith only [hdens]
    have hprod' : (Nat.card K:ℝ)^4*Real.exp (-b)≤(T.card:ℝ)*(S.map bidualPoint.toEmbedding).card := by
      rw [Finset.card_map];nlinarith only [hprod]
    have hh := (hbase D b τ R L₀ q K (Dual K V) hddual T UT
      (S.map bidualPoint.toEmbedding) (U.map bidualPoint.toEmbedding)
      hcard hσq hr hL hb hbhi hτ hτhi hTU hSU' hTS' hdens' hprod').2.2 t m hm
    simpa only [Finset.card_map,add_comm,add_left_comm,add_assoc] using hh
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open FiniteEntropy
open scoped Classical
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
noncomputable def FinitePredictor.transform (p : FinitePredictor A B) (e : A↪C)
    (inputs : Finset C→Finset D→Finset A×Finset B) : FinitePredictor C D where
  Tape := p.Tape
  tapeFintype := p.tapeFintype
  Message := p.Message
  messageFintype := p.messageFintype
  tapeLaw := p.tapeLaw
  decoded := fun t m=>(p.decoded t m).map e
  encoded := fun S T=>p.encoded (inputs S T).1 (inputs S T).2
  cost := p.cost
lemma FinitePredictor.transform_output (p : FinitePredictor A B) (e : A↪C)
    (inputs : Finset C→Finset D→Finset A×Finset B) (S : Finset C) (T : Finset D) :
    (p.transform e inputs).output S T=
      map (p.output (inputs S T).1 (inputs S T).2) (Option.map fun W=>W.map e) := by
  simp only [FinitePredictor.output,FinitePredictor.transform,map_comp,Option.map_map,Function.comp_def]
  rfl
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def threeFlatFinitePredictor (A : Submodule K V) (hA : finrank K A=4) (σ : ℝ)
    (UX : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (τ P : ℝ) (R : ℕ) (L₀ : ℝ≥0) (k : ℕ) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) := by
  letI : Finite A := Module.finite_of_finite K
  letI : Finite (Dual K A) := Module.finite_of_finite K
  letI : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI : Fintype (ℙ K A) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  exact (threeOrientedFinitePredictor hA σ (flatSection A UX) (planeEnclosure A UT k)
    P (Real.sqrt τ) R L₀).transform (flatEmbedding A)
      (fun X T=>(flatSection A X,planeHidden A X T τ k))

theorem eventually_three_flat_finite_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))],
    ∀ (A : Submodule K V) (hA : finrank K A=4)
      (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K V≤5 → Nat.card K=q → Real.exp σ=q →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-800*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      ∃k≤Nat.log 2 ((Nat.card K)^(finrank K V-finrank K A)),
        let pred := threeFlatFinitePredictor A hA σ UX UT τ (P η σ D R) R L₀ k
        let p := pred.output X T
        p none≤3*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
          (9/100000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m,pred.encoded X T t=some m→pred.cost t m≤
          30000*(Nat.card K:ℝ)*(P η σ D R)*
            (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+(P η σ D R))) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-400*beta η)<(1:ℝ)/200 := by
    have hp : 0<400*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<1/200)
  filter_upwards [eventually_three_finite_oriented hη hη' (Cb+1) (by linarith),
    eventually_restriction_overheads hη hη',ht,eventually_ge_atTop (1:ℝ)] with σ hbase hover ht hσ
  intro D b τ R L₀ q K V _ _ _ _ _ _ _ _ A hA X UX T UT hV hcard hσq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  let : Finite A := Module.finite_of_finite K
  let : Finite (Dual K A) := Module.finite_of_finite K
  let : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  let : Fintype (ℙ K A) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  let : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  have hq : (Nat.card K:ℝ)=Real.exp σ := by rw [hcard,hσq]
  have htroot : Real.sqrt τ≤σ^(-400*beta η) := by
    have hh := root_density_scale (j:=3) (d:=4) hσ hτ.le (beta_pos hη).le (by norm_num) (by norm_num)
      (show τ≤σ^(-200*(2:ℝ)^(4-2)*beta η) by norm_num;simpa only [neg_mul] using hτhi)
    convert hh using 1; norm_num
  have hsmall : Real.sqrt τ≤1/200 := htroot.trans ht.le
  obtain ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ :=
    original_large_cell A X UX T UT hX hT hXU hTU τ b hτ hsmall hflat hprod hdens
  let S := flatSection A X
  let US := flatSection A UX
  let M := (Nat.card K)^(finrank K V-finrank K A)
  let B := b+Real.log (400*(Nat.log 2 M+1:ℝ))
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  let pp := (threeOrientedFinitePredictor hA σ US UT₀ (P η σ D R) (Real.sqrt τ) R L₀).output S T₀
  have hB : 0≤B := by
    refine add_nonneg hb (Real.log_nonneg ?_)
    have hn : (0:ℝ)≤Nat.log 2 M := by positivity
    linarith only [hn]
  have hBhi : B≤(Cb+1)*D*σ^(6*beta η) :=
    (hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi).2.2
  have hp' : (Nat.card K:ℝ)^4*Real.exp (-B)≤(S.card:ℝ)*T₀.card := by
    simpa only [S,T₀,G,B,M,hA,Nat.cast_add,Nat.cast_one] using hp
  obtain ⟨hfail,hgood,hcost⟩ := hbase D B (Real.sqrt τ) R L₀ q K A hA S US T₀ UT₀ hT₀ hcard hσq hr hL
    hB hBhi (Real.sqrt_pos.mpr hτ) htroot hS hSU hTU₀ hd hp'
  refine ⟨k,hk,?_,?_,?_⟩
  · rw [threeFlatFinitePredictor,FinitePredictor.transform_output,map_option_none]
    exact hfail
  · intro W hW
    rw [threeFlatFinitePredictor,FinitePredictor.transform_output] at hW
    obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) hW
    cases Z with
    | none => simp at he
    | some Z =>
      have he' : Z.map (flatEmbedding A)=W := Option.some.inj he
      subst W
      have hz := hgood Z hZ
      obtain ⟨hu,hcard',hcap⟩ := section_decoder A X UX Z hz.1
      refine ⟨hu,?_,?_⟩
      · rw [hcard']
        exact hz.2.1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsX) (Real.exp_pos _).le)
      · rw [hcap,Finset.inter_comm]
        have hc := hz.2.2
        nlinarith only [hc,hxs]
  · intro t m hm
    have hc := hcost t m hm
    have hov := hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi
    have hP : 1≤P η σ D R :=
      (Real.one_le_rpow hσ (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
        (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
    have hlog : Real.log (400*(Nat.log 2 M+1:ℝ))≤P η σ D R := hov.2.1
    have h100 : Real.log (100:ℝ)≤P η σ D R := (Real.log_le_log (by norm_num) (by
      have hn : (0:ℝ)≤Nat.log 2 M := by positivity
      linarith : (100:ℝ)≤400*(Nat.log 2 M+1:ℝ))).trans hlog
    have h4 : Real.log (4*(Nat.log 2 M+1:ℝ))≤P η σ D R :=
      (Real.log_le_log (by positivity) (by
        have hn : (0:ℝ)≤Nat.log 2 M := by positivity
        linarith : (4:ℝ)*(Nat.log 2 M+1)≤400*(Nat.log 2 M+1:ℝ))).trans hlog
    have hgX : 0≤Real.log ((UX.card:ℝ)/X.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hX.card_pos)).mpr (by
        simpa using (show (X.card:ℝ)≤UX.card by exact_mod_cast Finset.card_le_card hXU)))
    have hgT : 0≤Real.log ((UT.card:ℝ)/T.card) := Real.log_nonneg
      ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr (by
        simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
    have hsum : Real.log ((US.card:ℝ)/S.card)+Real.log ((UT₀.card:ℝ)/T₀.card)+P η σ D R≤
        3*(Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by
      simp only [Nat.cast_add,Nat.cast_one] at hgap
      change _≤Real.log ((UT.card:ℝ)/T.card)+Real.log (4*(Nat.log 2 M+1:ℝ)) at hgap
      change _≤Real.log ((UX.card:ℝ)/X.card)+Real.log (100:ℝ) at hsgap
      linarith
    have hm' := mul_le_mul_of_nonneg_left hsum
      (by positivity : (0:ℝ)≤9000*(Nat.card K:ℝ)*P η σ D R)
    have hpos : 0≤(Nat.card K:ℝ)*P η σ D R*
        (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by positivity
    change (threeOrientedFinitePredictor hA σ US UT₀ (P η σ D R) (Real.sqrt τ) R L₀).cost t m≤_
    nlinarith only [hc,hm',hpos]
end SharpRamseyFive.ProjectiveRestriction

end OAI
