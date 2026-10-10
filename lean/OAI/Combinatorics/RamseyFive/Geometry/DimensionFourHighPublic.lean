import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Geometry.DimensionFourLowLaw
import OAI.Combinatorics.RamseyFive.Decoding.TwoPeelMessage

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy TrainingCells MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_high_public_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (2*σ+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) → P η σ D R/10000<g →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
    let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
    let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
    let _a := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
    let _e := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
    (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    ∃ Good : Set (Fin N→Fin R→ℙ K (I→K)→ℕ),
      (Measure.pi (fun _ : Fin N=>scheduleMeasure
        (fun x=>if x∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
         Goodᶜ ≤ Real.exp (-(Nat.card K:ℝ)) ∧
      ∀u∈Good,∃ i : Fin N,∃z : Fin (Fintype.card (ℙ K (Dual K (I→K)))+1),
        let W := publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)
        W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
        (9/40:ℝ)*X.card≤((W∩X).card:ℝ) := by
  have hh := eventually_four_high_training_score hη hη' Cb hCb
  have htau := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hp := (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<10) (beta_pos hη))).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hh,htau,hp,eventually_ge_atTop (100000:ℝ)] with σ hh htau hp hσ
  rw [←neg_mul] at htau
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover
  dsimp only
  let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
  let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
  let a := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
  let e := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
  let raw := twoPublicOwn (greedyList H hH (fun j=>flatPoints (Hyper j)) X h)
    (greedyList F hF (fun j=>flatPoints (Flat j)) XH p)
  change (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) → _
  intro hsmallH hsmallP
  have hp := hh D b τ g R L₀ q K I J F hF Flat H hH Hyper X U T
    hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover hsmallH hsmallP
  change S⊆X ∧ X.card≤4*S.card ∧ _ at hp
  obtain ⟨hSX,hret,hprob⟩ := hp
  have hHX : XH⊆X := peel_subset _ _ _ _ _ _ _
  have hSH : S⊆XH := peel_subset _ _ _ _ _ _ _
  have hret' : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
  have hSn : 0<(S.card:ℝ) := by nlinarith only [hret',hX,Real.exp_pos (2*σ+g)]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn)
  have hP : 4≤P η σ D R := hp.trans (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hq : 2<q := by exact_mod_cast (show (2:ℝ)<q by rw [←hσq];linarith only [Real.add_one_le_exp σ,hσ])
  have hqp : (0:ℝ)<Nat.card K := by rw [hcard,←hσq];exact Real.exp_pos _
  have hdim : finrank K (I→K)=4+1 := by rw [Module.finrank_pi,hI]
  have hm := sparse_half_rectangle_size (d:=4) hdim (by norm_num) (by omega : 3≤Nat.card K) X T (by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(Nat.card K:ℝ))).mpr
    have := mul_le_mul_of_nonneg_right (hτhi.trans htau.le) (by positivity : (0:ℝ)≤(X.card:ℝ)*T.card)
    nlinarith only [hdens,this])
  have hxx : (X.card:ℝ)^2≤16*Real.exp (5*σ) := by
    have hxt : (X.card:ℝ)≤T.card := by exact_mod_cast hXT
    have he : (Real.exp σ)^5=Real.exp (5*σ) := by rw [←Real.exp_nat_mul];norm_num
    rw [hcard,←hσq,he] at hm
    nlinarith
  have hnhi : (X.card:ℝ)≤4*Real.exp (5*σ/2) := by
    have he : (Real.exp (5*σ/2))^2=Real.exp (5*σ) := by rw [←Real.exp_nat_mul];congr 1;ring
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
    nlinarith only [hxx,he]
  have hghi : g≤σ/2+Real.log 4 := by
    have he : 2*σ+g≤5*σ/2+Real.log 4 := Real.exp_le_exp.mp (by
      rw [Real.exp_add (5*σ/2),Real.exp_log (by norm_num : (0:ℝ)<4)]
      nlinarith only [hnhi,hX])
    linarith only [he]
  obtain ⟨hcost,c,hOwn,hBase⟩ := two_peel_message σ g (P η σ D R)
    (by simpa only [Module.finrank_pi,hI] using le_refl 5) hσ
    (hσq.trans (by rw [hcard])) (by linarith only [hg,hP]) hghi H hH Hyper F hF Flat X hX
  have hd := literal_cell_data S X XH hSX hSH H hH (fun j=>flatPoints (Hyper j)) h F hF (fun j=>flatPoints (Flat j)) p
  change (∀i,family CH CP i⊆S) ∧ (∑i,(family CH CP i).card)≤3*S.card ∧
    (∀x,S∩raw x=CH (a x)∪CP (e x)) ∧ _ at hd
  have hO : ∀x,S∩messageOwn c x=CH (a x)∪CP (e x) := by
    intro x
    rw [hOwn]
    exact hd.2.2.1 x
  have hb' : (fun x=>Real.exp (-(L₀:ℝ)*(1-ownFraction S (CH (a x)) (CP (e x)))))=messageBase c L₀ := by
    funext x
    rw [hBase,hd.2.2.1 x]
    rfl
  rw [hb'] at hprob
  have hx := score_public_implementation U S hS (hSX.trans hXU) (fun x=>CH (a x)∪CP (e x))
    (messageOwn c) hO (messageBase c L₀) (exceptional S (family CH CP)) R L₀
    (P η σ D R) τ ((S.card:ℝ)*Real.exp (10*P η σ D R)) (by linarith only [hP]) hτ.le hprob
  dsimp only at hx
  let Good := ambientSuccess S (trueScoreSuccess U S (fun x=>CH (a x)∪CP (e x)) (messageBase c L₀)
    (exceptional S (family CH CP)) R (2*(Nat.card K:ℝ)*P η σ D R) ((S.card:ℝ)*Real.exp (10*P η σ D R)) ((9/10:ℝ)*S.card))
  refine ⟨?_,hx.1,c,{u | firstIndex Good u≠none},?_,?_⟩
  · simpa only [hcard] using hcost
  · simpa only [Set.compl_ofPred,not_not] using hx.2.1
  · intro u hu
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp hu
    obtain ⟨z,hz,_,hsize,hcapture⟩ := hx.2.2 u i hi
    have hz' : z<Fintype.card (ℙ K (Dual K (I→K)))+1 :=
      Nat.lt_succ_of_le (hz.trans (Finset.card_le_univ _))
    refine ⟨i,⟨z,hz'⟩,Finset.filter_subset _ _,?_,?_⟩
    · exact hsize.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSX) (Real.exp_pos _).le)
    · have hc : ((publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)∩S).card:ℝ)≤
          (publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)∩X).card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hSX)
      linarith only [hc,hcapture,hret']

end SharpRamseyFive.ScoreGeometry

end OAI
