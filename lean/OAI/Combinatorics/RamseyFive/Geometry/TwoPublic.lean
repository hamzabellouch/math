import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BaseFiniteCost

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_two_public_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [∀x : ℙ K V,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K V),Fintype (RadialLine x)],
    ∀ (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))) (_hT : T.Nonempty),
      finrank K V=3 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → S.Nonempty → S⊆U → T⊆UT →
      (Nat.card K:ℝ)*(incidences S T:ℝ)≤τ*S.card*T.card →
      (Nat.card K:ℝ)^3*Real.exp (-b)≤(S.card:ℝ)*T.card →
      ∃ n : Fin (1000*(Nat.card K)^2+1),
        n.val=reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card)) ∧
        let P₀ := P η σ D R
        let H := 1000*(Nat.card K)^2
        let encode := twoPublicEncoded S U T UT P₀ τ H n (Nat.card K)
          ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T.card) ((T.card:ℝ)*Real.exp (2*P₀))
        let decode := twoPublicDecoded U UT P₀ τ H (Nat.card K)
        let p := map (twoPublicLaw U UT P₀ τ R L₀ H (Nat.card K))
          (fun t=>(encode t).map (decode t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→ValidCap S U ((S.card:ℝ)*Real.exp (2*P₀)) W) ∧
        (∀t m,encode t=some m → twoPublicCost U UT P₀ τ H (Nat.card K) t m≤
          1300*(Nat.card K:ℝ)*P₀*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  filter_upwards [eventually_two_oriented hη hη' Cb hCb,
    eventually_reverse_parameters hη hη' Cb hCb,eventually_ge_atTop (1:ℝ)] with σ hgood hpar hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ _ _ _ _ S U T UT hT hdim hq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  have hn := reverseLength_universal_bound σ hσ hq.symm (by omega : finrank K V≤5) S U hS hSU
  refine ⟨⟨_,Nat.lt_succ_of_le hn⟩,rfl,?_⟩
  dsimp only
  have heq := twoPublic_oriented S U T UT hT (P η σ D R) τ R L₀ (1000*(Nat.card K)^2) hn
  have hg := hgood D b τ R L₀ K V S U T UT hT hdim hq hr hL hb hbhi hτ hτhi hS hSU hTU hdens hprod
  refine ⟨?_,?_,?_⟩
  · simpa only [heq] using hg.1
  · simpa only [heq] using hg.2
  · intro t m hm
    obtain ⟨hP,hbP,heP,hτsmall,hq3⟩ := hpar D R b τ hr hbhi hτ.le hτhi
    exact twoPublic_cost σ hσ hq.symm hdim S U hS hSU T UT hT hTU (P η σ D R) τ
      hP hτ.le (by linarith) _ hn t m hm
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ProjectiveRestriction
open Module ProjectiveIncidence ProjectiveTraining ScoreGeometry FiniteEntropy
open DyadicLifts ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology

theorem eventually_plane_public_complete {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)],
    ∀ (A : Submodule K V)
      [Fintype (ℙ K A)] [Fintype (ℙ K (Dual K A))]
      [Fintype (ℙ K (Dual K (Dual K A)))]
      [∀x : ℙ K A,Fintype (RadialLine x)]
      [∀x : ℙ K (Dual K A),Fintype (RadialLine x)],
    ∀ (X UX : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V))),
      finrank K A=3 → finrank K V≤5 → (Nat.card K:ℝ)=Real.exp σ →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-400*beta η) → X.Nonempty → T.Nonempty → X⊆UX → T⊆UT →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^(finrank K V)*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)≤100*(X∩flatPoints A).card →
      let S := flatSection A X
      let US := flatSection A UX
      let M := (Nat.card K)^(finrank K V-finrank K A)
      let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
      ∃ k, k≤Nat.log 2 M ∧
      let T₀ := restrictions (image A.dualRestrict) G k
      let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
      ∃ n : Fin (1000*(Nat.card K)^2+1),
        n.val=reverseLength (Nat.card K) (Real.log ((US.card:ℝ)/S.card)) ∧
        let P₀ := P η σ D R
        let H := 1000*(Nat.card K)^2
        let encode := twoPublicEncoded S US T₀ UT₀ P₀ (Real.sqrt τ) H n (Nat.card K)
          ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T₀.card) ((T₀.card:ℝ)*Real.exp (2*P₀))
        let decode := fun t m=>(twoPublicDecoded US UT₀ P₀ (Real.sqrt τ) H (Nat.card K) t m).map (flatEmbedding A)
        let p := map (twoPublicLaw US UT₀ P₀ (Real.sqrt τ) R L₀ H (Nat.card K))
          (fun t=>(encode t).map (decode t))
        p none≤2*Real.exp (-(Nat.card K:ℝ)) ∧
        (∀W,0<p (some W)→W⊆UX ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (2*P₀) ∧
          (9/1000:ℝ)*X.card≤(W∩X).card) ∧
        (∀t m, encode t=some m → twoPublicCost US UT₀ P₀ (Real.sqrt τ) H (Nat.card K) t m≤
          4000*(Nat.card K:ℝ)*P₀*(Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P₀)) := by
  have ht : ∀ᶠ σ : ℝ in atTop,σ^(-200*beta η)<(1:ℝ)/200 := by
    have hp : 0<200*beta η := mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul] using (tendsto_rpow_neg_atTop hp).eventually_lt_const
      (by norm_num : (0:ℝ)<1/200)
  filter_upwards [eventually_two_public_complete hη hη' (Cb+1) (by linarith),
    eventually_restriction_overheads hη hη',ht,eventually_ge_atTop (1:ℝ)] with σ hbase hover ht hσ
  intro D b τ R L₀ K V _ _ _ _ _ _ A _ _ _ _ _ X UX T UT hA hV hq hr hL hb hbhi hτ hτhi hX hT hXU hTU hdens hprod hflat
  have htroot : Real.sqrt τ≤σ^(-200*beta η) := by
    have hh := root_density_scale (j:=2) (d:=3) hσ hτ.le (beta_pos hη).le (by norm_num) (by norm_num)
      (show τ≤σ^(-200*(2:ℝ)^(3-2)*beta η) by norm_num;simpa only [neg_mul] using hτhi)
    simpa using hh
  have hsmall : Real.sqrt τ≤1/200 := htroot.trans ht.le
  obtain ⟨hS,hSU,hsX,hxs,k,hk,hT₀,hTU₀,hp,hdegrees,hd,hgap,hsgap⟩ :=
    original_large_cell A X UX T UT hX hT hXU hTU τ b hτ hsmall hflat hprod hdens
  dsimp only
  refine ⟨k,hk,?_⟩
  let S := flatSection A X
  let US := flatSection A UX
  let M := (Nat.card K)^(finrank K V-finrank K A)
  let B := b+Real.log (400*(Nat.log 2 M+1:ℝ))
  let G := nonzeroLifts A (goodLifts A S T (Real.sqrt τ/Nat.card K))
  let T₀ := restrictions (image A.dualRestrict) G k
  let UT₀ := enclosure (image A.dualRestrict) (nonzeroLifts A UT) (2^k)
  have hov := hover D R b Cb (Nat.card K) (finrank K V-finrank K A) hr hq (by omega) hbhi
  have hB : 0≤B := by
    refine add_nonneg hb (Real.log_nonneg ?_)
    have hn : (0:ℝ)≤Nat.log 2 M := by positivity
    linarith only [hn]
  have hBhi : B≤(Cb+1)*D*σ^(6*beta η) := hov.2.2
  have hp' : (Nat.card K:ℝ)^3*Real.exp (-B)≤(S.card:ℝ)*T₀.card := by
    simpa only [S,T₀,G,B,M,hA,Nat.cast_add,Nat.cast_one] using hp
  obtain ⟨n,hn,hfail,hgood,hcost⟩ := hbase D B (Real.sqrt τ) R L₀ K A S US T₀ UT₀ hT₀ hA hq hr hL
    hB hBhi (Real.sqrt_pos.mpr hτ) htroot hS hSU hTU₀ hd hp'
  refine ⟨n,hn,?_,?_,?_⟩
  · have hm := map_option_none
      (map (twoPublicLaw US UT₀ (P η σ D R) (Real.sqrt τ) R L₀ (1000*(Nat.card K)^2) (Nat.card K))
        (fun t=>(twoPublicEncoded S US T₀ UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) n (Nat.card K)
          ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T₀.card) ((T₀.card:ℝ)*Real.exp (2*P η σ D R)) t).map
          (twoPublicDecoded US UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K) t)))
      (fun Z=>Z.map (flatEmbedding A))
    rw [FiniteEntropy.map_comp] at hm
    simpa only [Function.comp_def,Option.map_map] using hm.le.trans hfail
  · intro W hW
    let tape := twoPublicLaw US UT₀ (P η σ D R) (Real.sqrt τ) R L₀ (1000*(Nat.card K)^2) (Nat.card K)
    let encode := twoPublicEncoded S US T₀ UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^3/T₀.card) ((T₀.card:ℝ)*Real.exp (2*P η σ D R))
    let decode := twoPublicDecoded US UT₀ (P η σ D R) (Real.sqrt τ) (1000*(Nat.card K)^2) (Nat.card K)
    let pp := map tape (fun t=>(encode t).map (decode t))
    have hw' : 0 < map pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) := by
      dsimp only [pp]
      rw [FiniteEntropy.map_comp]
      simpa only [Function.comp_def,Option.map_map] using hW
    obtain ⟨Z,hZ,he⟩ := map_positive pp (Option.map fun Z=>Z.map (flatEmbedding A)) (some W) hw'
    cases Z with
    | none => simp at he
    | some Z =>
      have he' : Z.map (flatEmbedding A)=W := Option.some.inj he
      subst W
      have hz := hgood Z hZ
      obtain ⟨hu,hcard,hcap⟩ := section_decoder A X UX Z hz.1
      refine ⟨hu,?_,?_⟩
      · rw [hcard]
        exact hz.2.1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsX) (Real.exp_pos _).le)
      · rw [hcap,Finset.inter_comm]
        have hc := hz.2.2
        nlinarith only [hc,hxs]
  · intro t m hm
    have hc := hcost t m hm
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
      (by positivity : (0:ℝ)≤1300*(Nat.card K:ℝ)*P η σ D R)
    have hpos : 0≤(Nat.card K:ℝ)*P η σ D R*
        (Real.log ((UX.card:ℝ)/X.card)+Real.log ((UT.card:ℝ)/T.card)+P η σ D R) := by positivity
    nlinarith only [hc,hm',hpos]
end SharpRamseyFive.ProjectiveRestriction

end OAI
