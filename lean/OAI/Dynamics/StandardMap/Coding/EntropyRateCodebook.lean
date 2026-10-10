import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.FiniteBinCoding
import OAI.Dynamics.StandardMap.Coding.TypicalWordCodebook

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [Fintype A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [DecidableEq A] in
theorem entropy_rate_codebook (f : X → X) (hf : MeasurePreserving f μ μ)
    (htotal : ∀ (m : ℕ), 0 < m → Ergodic (f^[m]) μ)
    (p : X → A) (hp : Measurable p) {δ : ℝ} (hδ : 0<δ) :
    ∃ m : ℕ, 0 < m ∧ ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
      ∃ S : Finset (Fin (n*m) → A),
        (S.card : ℝ)≤Real.exp ((n*m : ℕ)*(rate μ f p+δ)) ∧
        μ.real {x | word f p (n*m) x∉S}<ε := by
  have hlim := (tendsto_order.mp (rate_tendsto μ f hf p hp)).2
    (rate μ f p+δ/2) (by linarith)
  obtain ⟨m,hm,hmrate⟩ := (eventually_gt_atTop 0 |>.and hlim).exists
  have hmr : 0<(m : ℝ) := Nat.cast_pos.mpr hm
  have hblock : obs μ (word f p m)<(m : ℝ)*(rate μ f p+δ/2) := by
    exact (div_lt_iff₀ hmr).mp hmrate |>.trans_eq (mul_comm _ _)
  refine ⟨m,hm,?_⟩
  intro ε hε
  have htyp := eventually_upper_information_codebook μ (f^[m]) (htotal m hm)
    (word f p m) (word_measurable f hf.measurable p hp m)
    (δ:=(m : ℝ)*δ/2) (by positivity) hε
  filter_upwards [htyp] with n hn
  obtain ⟨B,hB,hbad⟩ := hn
  let S := B.map (wordPack n m).symm.toEmbedding
  have hmem (w : Fin (n*m) → A) : w∈S ↔ wordPack n m w∈B := by
    simp only [S,Finset.mem_map,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨b,hb,rfl⟩
      simpa using hb
    · intro hw
      exact ⟨wordPack n m w,hw,(wordPack n m).symm_apply_apply w⟩
  refine ⟨S,?_,?_⟩
  · have hcard : S.card=B.card := Finset.card_map _
    rw [hcard]
    apply hB.trans (Real.exp_le_exp.mpr ?_)
    have hn0 : (0 : ℝ)≤n := Nat.cast_nonneg n
    push_cast
    nlinarith
  · convert hbad using 1
    congr 1
    ext x
    simp only [mem_ofPred_eq,hmem,wordPack_apply]

end HyperbolicCoding

end
section
namespace HyperbolicCoding.Marker
open scoped BigOperators
variable {A C : Type*} {n r : ℕ}

def HeadMarker (hr : r < n) (zero one : A) (w : Fin n → A) : Prop :=
  (∀ j : Fin r, w ⟨j.val,lt_trans j.isLt hr⟩=zero) ∧ w ⟨r,hr⟩=one

def MarkedBlock (hr : r < n) (zero one : A) (w : Fin n → A) : Prop :=
  HeadMarker hr zero one w ∧
    ∀ j : Fin n,0 < j.val → ∃ (l : Fin r) (h : j.val+l.val < n), w ⟨j.val+l.val,h⟩=one

def centeredWindow (n : ℕ) (a : ℤ → A) (i : Fin n) : Fin (2*n) → A :=
  fun j => a ((i.val : ℤ)+(j.val : ℤ)-(n : ℤ))

def column (v : Fin (2*n) → A) (t : Fin n) : Fin n → A :=
  fun j => v ⟨n-t.val+j.val,by omega⟩

lemma column_centeredWindow (a : ℤ → A) (i t j : Fin n) :
    column (centeredWindow n a i) t j = a ((i.val : ℤ)-(t.val : ℤ)+(j.val : ℤ)) := by
  unfold column centeredWindow
  congr 1
  rw [Nat.cast_add,Nat.cast_sub (by omega : t.val≤n)]
  ring

lemma self_column_centeredWindow (a : ℤ → A) (i : Fin n) :
    column (centeredWindow n a i) i = fun j : Fin n => a (j.val : ℤ) := by
  funext j
  rw [column_centeredWindow,sub_self,zero_add]

noncomputable def candidates (hr : r < n) (zero one : A) (v : Fin (2*n) → A) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun t => HeadMarker hr zero one (column v t))

lemma mem_candidates (hr : r < n) (zero one : A) (v : Fin (2*n) → A) (t : Fin n) :
    t∈candidates hr zero one v ↔ HeadMarker hr zero one (column v t) := by
  classical
  simp [candidates]

noncomputable def phase (hn : 0 < n) (hr : r < n) (zero one : A) (v : Fin (2*n) → A) : Fin n :=
  if h : (candidates hr zero one v).Nonempty then (candidates hr zero one v).min' h
    else ⟨0,hn⟩

lemma phase_eq_of_no_earlier (hn : 0 < n) (hr : r < n) (zero one : A) (v : Fin (2*n) → A)
    (i : Fin n) (hi : HeadMarker hr zero one (column v i))
    (hbefore : ∀ t : Fin n,t < i → ¬HeadMarker hr zero one (column v t)) :
    phase hn hr zero one v=i := by
  classical
  have hm : i∈candidates hr zero one v := (mem_candidates hr zero one v i).mpr hi
  have hs : (candidates hr zero one v).Nonempty := ⟨i,hm⟩
  rw [phase,dite_eq_left hs]
  apply le_antisymm (Finset.min'_le _ _ hm)
  by_contra h
  have ht : (candidates hr zero one v).min' hs < i := lt_of_not_ge h
  exact hbefore _ ht ((mem_candidates hr zero one v _).mp (Finset.min'_mem _ hs))

theorem phase_centeredWindow (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (a : ℤ → A) (hblock : MarkedBlock hr zero one (fun j : Fin n => a (j.val : ℤ)))
    (i : Fin n) : phase hn hr zero one (centeredWindow n a i)=i := by
  apply phase_eq_of_no_earlier hn hr zero one _ i
  · rw [self_column_centeredWindow]
    exact hblock.1
  · intro t ht hm
    have hti : t.val < i.val := ht
    let j : Fin n := ⟨i.val-t.val,by omega⟩
    have hj : 0 < j.val := by dsimp [j]; omega
    obtain ⟨l,hl,hb⟩ := hblock.2 j hj
    have hz := hm.1 l
    rw [column_centeredWindow] at hz
    have heq : (i.val : ℤ)-(t.val : ℤ)+(l.val : ℤ) = ((j.val+l.val : ℕ) : ℤ) := by
      dsimp [j]
      omega
    rw [heq] at hz
    exact h01 (hz.symm.trans hb)

noncomputable def decodeWindow (hn : 0 < n) (hr : r < n) (zero one : A)
    (D : (Fin n → A) → (Fin n → C)) (v : Fin (2*n) → A) : C :=
  D (column v (phase hn hr zero one v)) (phase hn hr zero one v)

theorem decode_centeredWindow (hn : 0 < n) (hr : r < n) (zero one : A) (h01 : zero≠one)
    (D : (Fin n → A) → (Fin n → C)) (a : ℤ → A)
    (hblock : MarkedBlock hr zero one (fun j : Fin n => a (j.val : ℤ))) (i : Fin n) :
    decodeWindow hn hr zero one D (centeredWindow n a i)=D (fun j : Fin n => a (j.val : ℤ)) i := by
  unfold decodeWindow
  rw [phase_centeredWindow hn hr zero one h01 a hblock i,self_column_centeredWindow]

section Construction

def markWord (r : ℕ) (zero one : A) (w : Fin n → A) (i : Fin n) : A :=
  if i.val < r then zero else if i.val%r=0 ∨ i.val+1=n then one else w i

lemma exists_multiple_window (hr : 0 < r) (j : ℕ) :
    ∃ k : ℕ,j≤k ∧ k < j+r ∧ k%r=0 := by
  by_cases hj : j%r=0
  · exact ⟨j,le_rfl,by omega,hj⟩
  · have hm : j%r < r := Nat.mod_lt j hr
    have he := Nat.mod_add_div j r
    refine ⟨j+(r-j%r),by omega,by omega,?_⟩
    have hk : j+(r-j%r)=r*(j/r+1) := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [hk,Nat.mul_mod_right]

lemma exists_guard (hr0 : 0 < r) (hr : r < n) (j : Fin n) (hj : 0 < j.val) :
    ∃ k : Fin n, j.val≤k.val ∧ k.val < j.val+r ∧ r≤k.val ∧
      (k.val%r=0 ∨ k.val+1=n) := by
  by_cases hjr : j.val < r
  · exact ⟨⟨r,hr⟩,hjr.le,by dsimp only; omega,le_rfl,Or.inl (Nat.mod_self r)⟩
  · obtain ⟨k,hjk,hkr,hm⟩ := exists_multiple_window hr0 j.val
    by_cases hkn : k < n
    · exact ⟨⟨k,hkn⟩,hjk,hkr,(by dsimp only; omega),Or.inl hm⟩
    · refine ⟨⟨n-1,by omega⟩,by dsimp only; omega,by dsimp only; omega,by dsimp only; omega,Or.inr (by dsimp only; omega)⟩

theorem markWord_isMarked (hr0 : 0 < r) (hr : r < n) (zero one : A) (w : Fin n → A) :
    MarkedBlock hr zero one (markWord r zero one w) := by
  constructor
  · constructor
    · intro j
      simp only [markWord,j.isLt,↓reduceIte]
    · simp [markWord]
  · intro j hj
    obtain ⟨k,hjk,hkr,hrk,hk⟩ := exists_guard hr0 hr j hj
    let l : Fin r := ⟨k.val-j.val,by omega⟩
    have he : j.val+l.val=k.val := by dsimp [l]; omega
    refine ⟨l,by omega,?_⟩
    simp only [markWord,he,not_lt.mpr hrk,↓reduceIte,hk]

end Construction
end HyperbolicCoding.Marker

end
section
namespace HyperbolicCoding.Marker
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {n r : ℕ}

def reserved (n r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < r ∨ i.val%r=0 ∨ i.val+1=n)

omit [Fintype A] [DecidableEq A] in
lemma markWord_eq_outside (zero one : A) (w : Fin n → A) (i : Fin n)
    (hi : i∉reserved n r) : markWord r zero one w i=w i := by
  simp only [reserved,Finset.mem_filter,Finset.mem_univ,true_and,not_or] at hi
  simp only [markWord,hi.1,hi.2.1,hi.2.2,or_self,↓reduceIte]

lemma reserved_card (_hr : 0 < r) : (reserved n r).card ≤ r+n/r+2 := by
  let F : reserved n r → (Fin r ⊕ (Fin (n/r+1) ⊕ Unit)) := fun i =>
    if hi : i.val.val < r then Sum.inl ⟨i.val.val,hi⟩
    else if hd : i.val.val%r=0 then Sum.inr (Sum.inl ⟨i.val.val/r,by
      have h := Nat.div_le_div_right (Nat.le_of_lt i.val.isLt) (c:=r)
      omega⟩)
    else Sum.inr (Sum.inr ())
  have hF : Function.Injective F := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hi := (Finset.mem_filter.mp i.property).2
    have hj := (Finset.mem_filter.mp j.property).2
    by_cases hi₀ : i.val.val < r
    · by_cases hj₀ : j.val.val < r
      · simpa [F,hi₀,hj₀] using hij
      · simp only [F,dite_eq_left hi₀,dite_eq_right hj₀] at hij
        split_ifs at hij
    · by_cases hj₀ : j.val.val < r
      · simp only [F,dite_eq_right hi₀,dite_eq_left hj₀] at hij
        split_ifs at hij
      · by_cases hi₁ : i.val.val%r=0
        · by_cases hj₁ : j.val.val%r=0
          · have hquot : i.val.val/r=j.val.val/r := by
              simpa [F,hi₀,hj₀,hi₁,hj₁] using hij
            have hq1 := Nat.mod_add_div i.val.val r
            have hq2 := Nat.mod_add_div j.val.val r
            rw [hquot] at hq1
            omega
          · simp [F,hi₀,hj₀,hi₁,hj₁] at hij
        · by_cases hj₁ : j.val.val%r=0
          · simp [F,hi₀,hj₀,hi₁,hj₁] at hij
          · omega
  have h := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,
    ←Nat.add_assoc] using h

omit [Fintype A] [DecidableEq A] in
lemma markWord_cost (zero one : A) (w : Fin n → A) :
    nameCost w (markWord r zero one w) ≤ (reserved n r).card := by
  calc
    _ ≤ ∑ i : Fin n,if i∈reserved n r then (1 : ℝ) else 0 := by
      unfold nameCost
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i∈reserved n r
      · simp only [ite_eq_left hi]
        exact symbolCost_le_one _ _
      · rw [ite_eq_right hi,markWord_eq_outside zero one w i hi]
        simp [symbolCost]
    _ = _ := by simp

omit [Fintype A] [DecidableEq A] in
lemma markWord_cost_le (hr : 0 < r) (zero one : A) (w : Fin n → A) :
    nameCost w (markWord r zero one w) ≤ (r+n/r+2 : ℕ) :=
  (markWord_cost zero one w).trans (by exact_mod_cast reserved_card (n:=n) hr)

lemma overwrite_fiber_card (S : Finset (Fin n)) (f : (Fin n → A) → (Fin n → A))
    (hf : ∀ w i,i∉S → f w i=w i) (v : Fin n → A) :
    Fintype.card {w : Fin n → A // f w=v} ≤ (Fintype.card A)^S.card := by
  let F : {w : Fin n → A // f w=v} → (S → A) := fun w i => w.val i.val
  have hF : Function.Injective F := by
    intro w z hwz
    apply Subtype.ext
    funext i
    by_cases hi : i∈S
    · exact congrFun hwz ⟨i,hi⟩
    · calc
        w.val i = f w.val i := (hf w.val i hi).symm
        _ = v i := congrFun w.property i
        _ = f z.val i := (congrFun z.property i).symm
        _ = z.val i := hf z.val i hi
  simpa only [Fintype.card_fun,Fintype.card_coe] using Fintype.card_le_of_injective F hF

lemma markWord_fiber_card (zero one : A) (v : Fin n → A) :
    Fintype.card {w : Fin n → A // markWord r zero one w=v} ≤
      (Fintype.card A)^(reserved n r).card :=
  overwrite_fiber_card (reserved n r) (markWord r zero one)
    (markWord_eq_outside zero one) v

end HyperbolicCoding.Marker

end
section
namespace HyperbolicCoding
open Filter
open scoped Topology

lemma marked_entropy_exponent_bound (a h δ : ℝ) (ha : 1≤a) (K r m n : ℕ)
    (hr : 0<r)
    (hδ : (2*(K : ℝ)+1)*δ≤h/4)
    (hguard : ((K : ℝ)+1)*Real.log a/(r : ℝ)≤h/4) :
    2*Real.exp ((n*K*m : ℕ)*(h+δ))*a^(Marker.reserved (n*K*m+n*m) r).card*
      Real.exp (-((n*K*m+n*m : ℕ) : ℝ)*(h-δ)) ≤
      2*Real.exp (((r : ℝ)+2)*Real.log a-(n : ℝ)*m*(h/2)) := by
  let k := n*K*m
  let N := n*K*m+n*m
  let d := (Marker.reserved N r).card
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hlog : 0≤Real.log a := Real.log_nonneg ha
  have hrr : (0 : ℝ)<r := Nat.cast_pos.mpr hr
  have hd : (d : ℝ)≤(r : ℝ)+(N : ℝ)/r+2 := by
    have hd' : (d : ℝ)≤(r+N/r+2 : ℕ) := by exact_mod_cast Marker.reserved_card (n:=N) hr
    push_cast at hd'
    exact hd'.trans (by gcongr; exact Nat.cast_div_le)
  have he : (k : ℝ)*(h+δ)+(d : ℝ)*Real.log a-(N : ℝ)*(h-δ) ≤
      ((r : ℝ)+2)*Real.log a-(n : ℝ)*m*(h/2) := by
    calc
      _ ≤ (k : ℝ)*(h+δ)+((r : ℝ)+(N : ℝ)/r+2)*Real.log a-(N : ℝ)*(h-δ) := by gcongr
      _ = ((r : ℝ)+2)*Real.log a+(n : ℝ)*m*
          (-h+(2*(K : ℝ)+1)*δ+((K : ℝ)+1)*Real.log a/r) := by
        dsimp [k,N]
        push_cast
        field_simp
        ring
      _ ≤ _ := by
        have hh : -h+(2*(K : ℝ)+1)*δ+((K : ℝ)+1)*Real.log a/r ≤ -(h/2) := by linarith
        have hg := mul_le_mul_of_nonneg_left hh (show 0≤(n : ℝ)*m by positivity)
        linarith
  have hp : a^d=Real.exp ((d : ℝ)*Real.log a) := by rw [Real.exp_nat_mul,Real.exp_log ha0]
  change 2*Real.exp ((k : ℝ)*(h+δ))*a^d*Real.exp (-(N : ℝ)*(h-δ))≤_
  rw [hp,mul_assoc (2 : ℝ),mul_assoc (2 : ℝ),←Real.exp_add,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  convert he using 1
  ring

theorem exists_entropy_slack_parameters (a h ε : ℝ) (ha : 1≤a) (hh : 0<h) (hε : 0<ε) :
    ∃ K r : ℕ,0<K ∧ 0<r ∧ ∃ δ : ℝ,0<δ ∧
      (1 : ℝ)/(K+1 : ℕ)<ε ∧
      ∀ m : ℕ, 0 < m → ∀ M : ℝ, 0 < M → ∀ᶠ n : ℕ in atTop,
        0<n ∧ r<n*K*m+n*m ∧
        ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
        ((Marker.reserved (n*K*m+n*m) r).card : ℝ)/(n*K*m+n*m : ℕ)<ε ∧
        2*Real.exp ((n*K*m : ℕ)*(h+δ))*a^(Marker.reserved (n*K*m+n*m) r).card*
          Real.exp (-((n*K*m+n*m : ℕ) : ℝ)*(h-δ))<M := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1 : ℝ) (1/ε))
  have hKpos : 0<K := by exact_mod_cast lt_trans zero_lt_one ((le_max_left _ _).trans_lt hK)
  have hKR : 0<(K : ℝ)+1 := by positivity
  have htail : (1 : ℝ)/(K+1 : ℕ)<ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    have hg := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hK)
    push_cast
    nlinarith
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 (max (4*((K : ℝ)+1)*Real.log a/h) (4/ε)))
  have hrpos : 0<r := by exact_mod_cast lt_trans zero_lt_one ((le_max_left _ _).trans_lt hr)
  have hrr : (0 : ℝ)<r := Nat.cast_pos.mpr hrpos
  have hguard : ((K : ℝ)+1)*Real.log a/r≤h/4 := by
    apply (div_le_iff₀ hrr).mpr
    have hg := (div_lt_iff₀ hh).mp
      ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hr))
    nlinarith
  have hrsmall : (1 : ℝ)/r<ε/4 := by
    apply (div_lt_iff₀ hrr).mpr
    have hg := (div_lt_iff₀ hε).mp
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hr))
    nlinarith
  let δ : ℝ := h/(8*((K : ℝ)+1))
  have hδpos : 0<δ := div_pos hh (by positivity)
  have hδ : (2*(K : ℝ)+1)*δ≤h/4 := by
    have heq : (8*((K : ℝ)+1))*δ=h := by dsimp [δ]; field_simp
    have hg : 0≤δ := hδpos.le
    nlinarith
  refine ⟨K,r,hKpos,hrpos,δ,hδpos,htail,?_⟩
  intro m hm M hM
  let C := ((r : ℝ)+2)*Real.log a
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max ((r : ℝ)+1)
    (max (4*((r : ℝ)+2)/ε) (2*(C-Real.log (M/2))/h)))
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hnr : (n₀ : ℝ)≤n := by exact_mod_cast hn
  have hlarge := hn₀.trans_le hnr
  have hnr' : (r : ℝ)+1<(n : ℝ) := (le_max_left _ _).trans_lt hlarge
  have hnp : 0 < n := by
    exact_mod_cast (lt_trans (by positivity : (0 : ℝ)<(r : ℝ)+1) hnr')
  have hnm : n≤n*m := Nat.le_mul_of_pos_right n hm
  have hnN : n≤n*K*m+n*m := hnm.trans (Nat.le_add_left _ _)
  have hnNR : (n : ℝ)≤(n*K*m+n*m : ℕ) := by exact_mod_cast hnN
  have hnR : (0 : ℝ)<n := Nat.cast_pos.mpr hnp
  have hN : (0 : ℝ)<(n*K*m+n*m : ℕ) := hnR.trans_le hnNR
  refine ⟨hnp,?_,?_,?_,?_⟩
  · have : r<n := by exact_mod_cast (show (r : ℝ)<n by linarith)
    exact this.trans_le hnN
  · have hem : ((n*m : ℕ) : ℝ)/(n*K*m+n*m : ℕ)=(1 : ℝ)/(K+1 : ℕ) := by
      push_cast
      have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
      field_simp
    simpa only [hem] using htail
  · have hd : ((Marker.reserved (n*K*m+n*m) r).card : ℝ)≤
        (r : ℝ)+((n*K*m+n*m : ℕ) : ℝ)/r+2 := by
      have hd' : ((Marker.reserved (n*K*m+n*m) r).card : ℝ)≤(r+(n*K*m+n*m)/r+2 : ℕ) :=
        by exact_mod_cast Marker.reserved_card (n:=n*K*m+n*m) hrpos
      push_cast at hd'
      exact hd'.trans (by gcongr; exact Nat.cast_div_le)
    have hsmall : ((r : ℝ)+2)/((n*K*m+n*m : ℕ) : ℝ)<ε/4 := by
      apply (div_lt_iff₀ hN).mpr
      have ht := (div_lt_iff₀ hε).mp
        ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hlarge))
      have hg := mul_le_mul_of_nonneg_left hnNR hε.le
      nlinarith
    have hdivide := div_le_div_of_nonneg_right hd hN.le
    have heq : ((r : ℝ)+((n*K*m+n*m : ℕ) : ℝ)/r+2)/((n*K*m+n*m : ℕ) : ℝ)=
        ((r : ℝ)+2)/((n*K*m+n*m : ℕ) : ℝ)+(1 : ℝ)/r := by field_simp; ring
    rw [heq] at hdivide
    linarith
  · apply lt_of_le_of_lt (marked_entropy_exponent_bound a h δ ha K r m n hrpos hδ hguard)
    have ht := (div_lt_iff₀ hh).mp
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hlarge))
    have hnmR : (n : ℝ)≤(n : ℝ)*m := by exact_mod_cast hnm
    have hg := mul_le_mul_of_nonneg_right hnmR hh.le
    have hexp : C-(n : ℝ)*m*(h/2)<Real.log (M/2) := by nlinarith
    have he := Real.exp_lt_exp.mpr hexp
    rw [Real.exp_log (by positivity : 0<M/2)] at he
    change 2*Real.exp (C-(n : ℝ)*m*(h/2))<M
    linarith

end HyperbolicCoding

end

end OAI
