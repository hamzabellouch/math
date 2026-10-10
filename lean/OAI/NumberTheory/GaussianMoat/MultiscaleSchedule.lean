import OAI.NumberTheory.GaussianMoat.Information

namespace OAI

universe uOmega uAlpha

namespace GaussianMoat
open scoped BigOperators Classical

structure EnrichmentMargins (s : SplitSieve) (D g : ℝ) (n b q : ℕ) : Prop where
  length_pos : 1 ≤ n
  output_pos : 0 < b
  decreases : b < q
  input_cap : q ≤ s.primes.card
  ratio : (b:ℝ) ≤ g*q
  log_pos : 0 < Real.log n-Real.log 18
  rounding : s.meanLog ≤ g*(Real.log n-Real.log 18)
  large : 5120*s.meanLog ≤ g^4*(Real.log n-Real.log 18)
  output_cost : (b:ℝ)*s.meanLog ≤ g*(Real.log n-Real.log 18)
  lattice_cost : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤
    g*(Real.log n-Real.log 18)
  geometry_cap : 2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*s.meanLog
  displacement_cost : 2*(Real.log 36+2*Real.log (D*n)) ≤ 8*g*q*s.meanLog

theorem TimeLaw.geometric_step_deficit (P : TimeLaw) (s : SplitSieve)
    (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    {D T g e : ℝ} (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog) {n b q : ℕ}
    (hm : EnrichmentMargins s D g n b q)
    (hE : (1-e)*(q:ℝ)*s.meanLog ≤ s.pointEntropy P.law (fun a => z a.val) q) :
    (1-e/2-20*g)*(b:ℝ)*s.meanLog ≤
      s.pointEntropy (P.step z n).law (fun a => z a.val) b := by
  apply P.step_deficit s z hD hstep hm.length_pos hm.output_pos hm.decreases
    hm.input_cap hg.le hg1 (by linarith only [hL]) hm.ratio ?_ hE hm.displacement_cost
  intro a
  obtain ⟨hb,hh⟩ := s.walk_fresh_lower hne (fun t => z (a.val+t)) hm.length_pos
    (shifted_walk_injective z hinj a.val) hD hT
    (fun t _ => by simpa only [Nat.add_assoc] using hstep (a.val+t)) hpT hg hg1 hL
    hm.log_pos hm.rounding hm.large hm.output_cost hm.lattice_cost hm.geometry_cap
  exact hh

lemma SplitSieve.pointEntropy_nonneg {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (Z : Ω → GaussianInt) (b : ℕ) :
    0 ≤ s.pointEntropy p Z b := by
  unfold pointEntropy FinLaw.signedEntropy
  exact Finset.expect_nonneg (fun _ _ => p.orderedEntropy_nonneg _ _)

noncomputable def TimeLaw.run (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ → ℕ) : ℕ → TimeLaw
  | 0 => P
  | j+1 => (P.run z n j).step z (n j)

@[simp] lemma TimeLaw.run_zero (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ → ℕ) :
    P.run z n 0=P := rfl
@[simp] lemma TimeLaw.run_succ (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ → ℕ) (j : ℕ) :
    P.run z n (j+1)=(P.run z n j).step z (n j) := rfl

theorem TimeLaw.run_entropy (P : TimeLaw) (s : SplitSieve) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hinj : Function.Injective z) {D T g : ℝ}
    (hD : 1 ≤ D) (hT : 5 ≤ T) (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog)
    (n q : ℕ → ℕ) (l : ℕ) (hm : ∀ j<l, EnrichmentMargins s D g (n j) (q (j+1)) (q j)) :
    (1-(1/2:ℝ)^l-40*g)*(q l:ℝ)*s.meanLog ≤
      s.pointEntropy (P.run z n l).law (fun a => z a.val) (q l) := by
  induction l with
  | zero =>
    have hh := s.pointEntropy_nonneg P.law (fun a => z a.val) (q 0)
    simp only [pow_zero,sub_self,zero_sub,TimeLaw.run_zero]
    have hneg : -(40*g)*(q 0:ℝ)*s.meanLog ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hg]) (Nat.cast_nonneg (q 0))
      · linarith only [hL]
    exact hneg.trans hh
  | succ l ih =>
    have hi := ih (fun j hj => hm j (by omega))
    have hh := (P.run z n l).geometric_step_deficit s hne z hinj hD hT hstep hpT
      hg hg1 hL (hm l (by omega)) (e := (1/2:ℝ)^l+40*g) (by
        convert hi using 1; ring)
    rw [TimeLaw.run_succ]
    convert hh using 1; ring

theorem TimeLaw.advance_entropy (P : TimeLaw) (K : ForwardKernel) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) (b : ℕ) :
    s.pointEntropy P.law (fun a => z a.val) b -
      (Real.log 36+2*Real.log (D*K.bound)) ≤
    s.pointEntropy (P.advance K).law (fun a => z a.val) b := by
  let Q := P.law.joint (fun a => K.law a.val)
  have hh := s.pointEntropy_shift Q (fun v => z v.1.val)
    (fun v => z (v.1.val+v.2.val)) b
  have hfst := s.pointEntropy_joint_fst P.law (fun a => K.law a.val) (fun a => z a.val) b
  change s.pointEntropy Q (fun v => z v.1.val) b = _ at hfst
  rw [hfst] at hh
  have he : s.pointEntropy (P.advance K).law (fun a => z a.val) b =
      s.pointEntropy Q (fun v => z (v.1.val+v.2.val)) b := by
    unfold TimeLaw.advance
    rw [s.pointEntropy_map]
    rfl
  rw [he]
  have hc := P.advance_displacement_entropy K z hD hstep hK
  linarith only [hh,hc]

theorem TimeLaw.run_future_entropy (P : TimeLaw) (K : ForwardKernel) (s : SplitSieve)
    (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    {D T g : ℝ} (hD : 1 ≤ D) (hT : 5 ≤ T)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D)
    (hpT : ∀ p ∈ s.primes, T ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*T)
    (hg : 0 < g) (hg1 : g ≤ 1/100) (hL : 1 ≤ s.meanLog)
    (n q : ℕ → ℕ) (l : ℕ) (hm : ∀ j<l, EnrichmentMargins s D g (n j) (q (j+1)) (q j))
    (hK : 1 ≤ K.bound) {e : ℝ}
    (hcost : Real.log 36+2*Real.log (D*K.bound) ≤ e*(q l:ℝ)*s.meanLog) :
    (1-(1/2:ℝ)^l-40*g-e)*(q l:ℝ)*s.meanLog ≤
      s.pointEntropy ((P.run z n l).advance K).law (fun a => z a.val) (q l) := by
  have h1 := P.run_entropy s hne z hinj hD hT hstep hpT hg hg1 hL n q l hm
  have h2 := (P.run z n l).advance_entropy K s z hD hstep hK (q l)
  nlinarith only [h1,h2,hcost]

noncomputable def TimeLaw.observe {α : Type uAlpha} [Fintype α] (P : TimeLaw) (f : ℕ → α) : FinLaw α :=
  P.law.map (fun t => f t.val)

lemma TimeLaw.ext_observe (P Q : TimeLaw) (hl : P.last=Q.last)
    (h : ∀ {α : Type} [Fintype α] (f : ℕ → α), P.observe f=Q.observe f) : P=Q := by
  cases P with | mk n p =>
  cases Q with | mk m q =>
  dsimp only at hl
  subst m
  congr 1
  let f : ℕ → Fin (n+1) := fun t => ⟨min t n,by omega⟩
  have hh := h f
  have he : (fun t : Fin (n+1) => f t.val)=id := by
    funext t
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  unfold observe at hh
  simpa only [he,FinLaw.map_id] using hh

lemma TimeLaw.observe_advance {α : Type uAlpha} [Fintype α]
    (P : TimeLaw) (K : ForwardKernel) (f : ℕ → α) :
    (P.advance K).observe f=P.law.mix (fun a => (K.law a.val).map (fun t => f (a.val+t.val))) := by
  unfold observe advance
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  rfl

lemma ForwardKernel.then_observe {α : Type uAlpha} [Fintype α]
    (K R : ForwardKernel) (a : ℕ) (f : ℕ → α) :
    ((K.then R).law a).map (fun t => f (a+t.val))=
      (K.law a).mix (fun t => (R.law (a+t.val)).map (fun u => f (a+t.val+u.val))) := by
  unfold ForwardKernel.then
  rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  congr 1
  funext t
  congr 1
  funext u
  simp only [Function.comp_def,addOffsets,Nat.add_assoc]

lemma TimeLaw.advance_then (P : TimeLaw) (K R : ForwardKernel) :
    P.advance (K.then R)=(P.advance K).advance R := by
  apply TimeLaw.ext_observe
  · exact (Nat.add_assoc _ _ _).symm
  · intro α _ f
    rw [TimeLaw.observe_advance,TimeLaw.observe_advance]
    change P.law.mix _ = (((P.law.joint (fun a => K.law a.val)).map
      (addOffsets P.last K.bound))).mix (fun a : Fin (P.last+K.bound+1) =>
        (R.law a.val).map (fun t => f (a.val+t.val)))
    rw [FinLaw.mix_map_left]
    have hj := FinLaw.joint_observation (P.law) (fun a => K.law a.val)
      (fun a t => (a,t))
    clear hj
    have hmix : ((P.law.joint (fun a => K.law a.val))).mix
        (fun v => (R.law (v.1.val+v.2.val)).map (fun u => f (v.1.val+v.2.val+u.val))) =
      P.law.mix (fun a => (K.law a.val).mix
        (fun t => (R.law (a.val+t.val)).map (fun u => f (a.val+t.val+u.val)))) := by
      ext x
      simp only [FinLaw.mix_mass,FinLaw.joint_mass,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
    change P.law.mix _ = (P.law.joint (fun a => K.law a.val)).mix
      (fun v => (R.law (v.1.val+v.2.val)).map (fun u => f (v.1.val+v.2.val+u.val)))
    rw [hmix]
    congr 1
    funext a
    exact K.then_observe R a.val f

lemma TimeLaw.advance_common_cons (P : TimeLaw) (z : ℕ → GaussianInt)
    (n : ℕ) (ns : List ℕ) (N : ℕ) :
    P.advance (commonSchedule z (n::ns) N)=(P.step z n).advance (commonSchedule z ns N) := by
  rw [commonSchedule_cons,TimeLaw.advance_then,TimeLaw.advance_difference]

lemma TimeLaw.advance_common_append (P : TimeLaw) (z : ℕ → GaussianInt)
    (ns ms : List ℕ) (N : ℕ) :
    P.advance (commonSchedule z (ns++ms) N)=
      (ns.foldl (fun Q k => Q.step z k) P).advance (commonSchedule z ms N) := by
  induction ns generalizing P with
  | nil => rfl
  | cons k ks hk =>
    rw [List.cons_append,TimeLaw.advance_common_cons,hk,List.foldl_cons]

lemma TimeLaw.foldl_ofFn (P : TimeLaw) (z : ℕ → GaussianInt)
    (n : ℕ → ℕ) (l : ℕ) :
    (List.ofFn (fun i : Fin l => n i.val)).foldl (fun Q k => Q.step z k) P=P.run z n l := by
  induction l with
  | zero => rfl
  | succ l hl =>
    rw [List.ofFn_succ_last,List.foldl_append,List.foldl_cons,List.foldl_nil]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [hl,TimeLaw.run_succ]

lemma TimeLaw.run_common (P : TimeLaw) (z : ℕ → GaussianInt)
    (n : ℕ → ℕ) (l N : ℕ) :
    P.advance (commonSchedule z (List.ofFn (fun i : Fin l => n i.val)) N)=
      (P.run z n l).advance (smoothingKernel N) := by
  have h := P.advance_common_append z (List.ofFn (fun i : Fin l => n i.val)) [] N
  simpa only [List.append_nil,TimeLaw.foldl_ofFn,commonSchedule,List.foldr_nil] using h

lemma log_floor_exp {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ ⌊Real.exp x⌋₊ ∧ x-1 ≤ Real.log (⌊Real.exp x⌋₊:ℝ) ∧
      Real.log (⌊Real.exp x⌋₊:ℝ) ≤ x := by
  have he : 2 ≤ Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hn : 1 ≤ ⌊Real.exp x⌋₊ := Nat.floor_pos.mpr (by linarith only [he])
  have hnp : (0:ℝ)<⌊Real.exp x⌋₊ := by exact_mod_cast hn
  have hlow : Real.exp x/2 ≤ (⌊Real.exp x⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp x)
    linarith only [he,h]
  have hlo := Real.log_le_log (div_pos (Real.exp_pos x) (by norm_num : (0:ℝ)<2)) hlow
  rw [Real.log_div (Real.exp_ne_zero x) (by norm_num : (2:ℝ)≠0),Real.log_exp] at hlo
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [h]
  have hhi := Real.log_le_log hnp (Nat.floor_le (Real.exp_nonneg x))
  rw [Real.log_exp] at hhi
  exact ⟨hn,by linarith only [hlo,hl2],hhi⟩

theorem EnrichmentMargins.from_scale (s : SplitSieve) {D U g : ℝ}
    (hD : 1 ≤ D) (hg : 0 < g) (hg1 : g ≤ 1/200) (hL : 1 ≤ s.meanLog)
    (hU : 0 < U)
    (hlog : 2*(1+Real.log 18) ≤ g*U)
    (hlarge : 640*s.meanLog ≤ g^5*U)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤ g^2*U)
    (hdisp : 4*Real.log D+2*Real.log 36 ≤ 4*g*U)
    (hgeom : 2*Real.log 16+4*Real.log D ≤ U/4)
    (hcap : ⌊U/s.meanLog⌋₊ ≤ s.primes.card) :
    EnrichmentMargins s D (2*g) ⌊Real.exp (g*U)⌋₊
      ⌊g^2*U/s.meanLog⌋₊ ⌊U/s.meanLog⌋₊ := by
  let L := s.meanLog
  let n := ⌊Real.exp (g*U)⌋₊
  let q := ⌊U/L⌋₊
  let b := ⌊g^2*U/L⌋₊
  have hLp : 0 < L := by dsimp [L]; linarith only [hL]
  have hg_le : g ≤ 1 := by linarith only [hg1]
  have hg2 : g^2 ≤ 1 := pow_le_one₀ hg.le hg_le
  have hg3 : g^3 ≤ 1 := pow_le_one₀ hg.le hg_le
  have h52 : g^5*U ≤ g^2*U := by
    have hpow : g^5=g^2*g^3 := by ring
    rw [hpow]
    nlinarith only [hg3,mul_nonneg (sq_nonneg g) hU.le]
  have h2U : g^2*U ≤ U := by nlinarith only [hg2,hU]
  have hLU : L ≤ U/2 := by
    change 640*L ≤ g^5*U at hlarge
    linarith only [hlarge,h52,h2U,hLp]
  have hbL : L ≤ g^2*U := by
    change 640*L ≤ g^5*U at hlarge
    linarith only [hlarge,h52,hLp]
  have he2 : 2 ≤ g*U := by
    have hh := Real.log_nonneg (by norm_num : (1:ℝ)≤18)
    linarith only [hh,hlog]
  obtain ⟨hn,hnlo,hnhi⟩ := log_floor_exp he2
  have hnlo' : g*U/2 ≤ Real.log n-Real.log 18 := by
    change g*U-1 ≤ Real.log n at hnlo
    linarith only [hnlo,hlog]
  have hu : 0 < Real.log n-Real.log 18 :=
    lt_of_lt_of_le (div_pos (mul_pos hg hU) (by norm_num)) hnlo'
  have hqL : U-L ≤ (q:ℝ)*L := by
    have hf := Nat.lt_floor_add_one (U/L)
    have hm := mul_lt_mul_of_pos_right hf hLp
    rw [div_mul_cancel₀ _ hLp.ne',add_mul,one_mul] at hm
    linarith only [hm]
  have hqU : U/2 ≤ (q:ℝ)*L := by linarith only [hqL,hLU]
  have hqpos : 0 < q := by
    have : (0:ℝ)<q := by nlinarith only [hqU,hU,hLp]
    exact_mod_cast this
  have hbpos : 0 < b := by
    apply Nat.floor_pos.mpr
    exact (le_div_iff₀ hLp).mpr (by simpa only [one_mul] using hbL)
  have hbup : (b:ℝ)*L ≤ g^2*U := by
    exact (le_div_iff₀ hLp).mp (Nat.floor_le (by positivity : 0 ≤ g^2*U/L))
  have hratio : (b:ℝ) ≤ (2*g)*q := by
    have h1 := mul_le_mul_of_nonneg_left hqU (show 0 ≤ 2*g by positivity)
    have h2 : g^2*U ≤ g*U := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg_le hg.le) hU.le
      simpa only [mul_one,pow_two] using hh
    apply (mul_le_mul_iff_left₀ hLp).mp
    nlinarith only [hbup,h1,h2]
  have hbq : b < q := by
    have hqr : (0:ℝ)<q := by exact_mod_cast hqpos
    have : (b:ℝ)<q := by nlinarith only [hratio,hg1,hqr]
    exact_mod_cast this
  refine ⟨hn,hbpos,hbq,hcap,hratio,hu,?_,?_,?_,?_,?_,?_⟩
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    dsimp only [L] at hbL
    nlinarith only [hbL,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ (2*g)^4 by positivity)
    nlinarith only [hlarge,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    change (b:ℝ)*L ≤ _
    nlinarith only [hbup,hm]
  · have hm := mul_le_mul_of_nonneg_left hnlo' (show 0 ≤ 2*g by positivity)
    linarith only [hsize,hm]
  · have hqcap : (q:ℝ)*L ≤ s.primes.card*L :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcap) hLp.le
    have hgU := mul_le_mul_of_nonneg_right hg1 hU.le
    change 2*(2*Real.log n+Real.log 16+2*Real.log D) ≤ s.primes.card*L
    change Real.log n ≤ g*U at hnhi
    nlinarith only [hnhi,hgeom,hqU,hqcap,hgU,hU]
  · have hm := mul_le_mul_of_nonneg_left hqU (show 0 ≤ 16*g by positivity)
    have hDn : D≠0 := by linarith only [hD]
    have hnR : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
    rw [Real.log_mul hDn hnR]
    change Real.log n ≤ g*U at hnhi
    change 2*(Real.log 36+2*(Real.log D+Real.log n)) ≤ 8*(2*g)*q*L
    nlinarith only [hnhi,hdisp,hm]

noncomputable def bandScale (g U : ℝ) (j : ℕ) : ℝ := (g^2)^j*U
noncomputable def bandLength (g U : ℝ) (j : ℕ) : ℕ := ⌊Real.exp (g*bandScale g U j)⌋₊
noncomputable def bandSize (s : SplitSieve) (g U : ℝ) (j : ℕ) : ℕ := ⌊bandScale g U j/s.meanLog⌋₊

lemma bandScale_pos {g U : ℝ} (hg : 0<g) (hU : 0<U) (j : ℕ) :
    0<bandScale g U j := mul_pos (pow_pos (sq_pos_of_pos hg) _) hU

lemma bandScale_antitone {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U) :
    Antitone (bandScale g U) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sq_nonneg g) (pow_le_one₀ hg hg1) hij) hU

lemma bandScale_succ (g U : ℝ) (j : ℕ) :
    bandScale g U (j+1)=g^2*bandScale g U j := by
  unfold bandScale
  rw [pow_succ]
  ring

theorem geometric_band_margins (s : SplitSieve) {D U g : ℝ} {l : ℕ}
    (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200) (hL : 1 ≤ s.meanLog) (hU : 0<U)
    (hlog : 2*(1+Real.log 18) ≤ g*bandScale g U l)
    (hlarge : 640*s.meanLog ≤ g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤ g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36 ≤ 4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D ≤ bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊ ≤ s.primes.card) :
    ∀ j<l, EnrichmentMargins s D (2*g) (bandLength g U j)
      (bandSize s g U (j+1)) (bandSize s g U j) := by
  intro j hj
  have hmono := bandScale_antitone hg.le (show g≤1 by linarith only [hg1]) hU.le
  have hlow := hmono hj.le
  have hhigh := hmono (Nat.zero_le j)
  simp only [bandScale,pow_zero,one_mul] at hhigh
  unfold bandLength bandSize
  rw [bandScale_succ]
  apply EnrichmentMargins.from_scale s hD hg hg1 hL (bandScale_pos hg hU j)
  · exact hlog.trans (mul_le_mul_of_nonneg_left hlow hg.le)
  · exact hlarge.trans (mul_le_mul_of_nonneg_left hlow (pow_nonneg hg.le _))
  · exact hsize.trans (mul_le_mul_of_nonneg_left hlow (sq_nonneg g))
  · exact hdisp.trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  · exact hgeom.trans (div_le_div_of_nonneg_right hlow (by norm_num))
  · exact (Nat.floor_mono (div_le_div_of_nonneg_right hhigh (by linarith only [hL]))).trans hcap

theorem TimeLaw.geometric_band_entropy (P : TimeLaw) (s : SplitSieve)
    (hne : s.primes.Nonempty) (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    {D T U g : ℝ} {l : ℕ} (hD : 1≤D) (hT : 5≤T)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hg : 0<g) (hg1 : g≤1/200) (hL : 1 ≤ s.meanLog) (hU : 0<U)
    (hlog : 2*(1+Real.log 18) ≤ g*bandScale g U l)
    (hlarge : 640*s.meanLog ≤ g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ)) ≤ g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36 ≤ 4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D ≤ bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊ ≤ s.primes.card) :
    (1-(1/2:ℝ)^l-80*g)*(bandSize s g U l:ℝ)*s.meanLog ≤
      s.pointEntropy (P.run z (bandLength g U) l).law (fun a => z a.val) (bandSize s g U l) := by
  have hm := geometric_band_margins s hD hg hg1 hL hU hlog hlarge hsize hdisp hgeom hcap
  have hh := P.run_entropy s hne z hinj hD hT hs hpT (by positivity : 0<2*g)
    (by linarith only [hg1] : 2*g≤1/100) hL (bandLength g U) (bandSize s g U) l hm
  convert hh using 1; ring

lemma commonSchedule_log_bound (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) {x : ℝ}
    (hns : ∀ n∈ns, (n:ℝ)≤Real.exp x) (hN : (N:ℝ)≤Real.exp x)
    (hlen : (ns.length+2:ℝ)≤Real.exp x) :
    Real.log (1+(commonSchedule z ns N).bound:ℝ) ≤ 2*x := by
  have hsum : (ns.sum:ℝ)≤(ns.length:ℝ)*Real.exp x := by
    induction ns with
    | nil => simp
    | cons n ns ih =>
      have hn := hns n (by simp)
      have ht := ih (fun k hk => hns k (by simp [hk]))
        (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hlen; linarith only [hlen])
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hn,ht]
  have hx : (1:ℝ)≤Real.exp x := by
    have hlen0 : (0:ℝ)≤ns.length := Nat.cast_nonneg _
    linarith only [hlen,hlen0]
  have hall : (1+(commonSchedule z ns N).bound:ℝ)≤Real.exp (2*x) := by
    rw [commonSchedule_bound,Nat.cast_add]
    have hm := mul_le_mul_of_nonneg_right hlen (Real.exp_nonneg x)
    rw [show 2*x=x+x by ring,Real.exp_add]
    nlinarith only [hsum,hN,hm,hx]
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<1+(commonSchedule z ns N).bound) hall
  simpa only [Real.log_exp] using hlog

lemma suffix_entropy_cost {D g V L : ℝ} {q S : ℕ}
    (hD : 1≤D) (hg : 0≤g) (hS : 1≤S)
    (hq : V/2≤(q:ℝ)*L) (hlog : Real.log (1+(S:ℝ))≤2*g*V)
    (hconst : Real.log 36+2*Real.log D≤g*V) :
    Real.log 36+2*Real.log (D*S)≤10*g*q*L := by
  have hSp : (0:ℝ)<S := by exact_mod_cast hS
  have hSl := Real.log_le_log hSp (show (S:ℝ)≤1+S by linarith)
  rw [Real.log_mul (by linarith only [hD] : D≠0) hSp.ne']
  have hq' := mul_le_mul_of_nonneg_left hq (show 0≤10*g by positivity)
  nlinarith only [hSl,hlog,hconst,hq']

end GaussianMoat

end OAI
