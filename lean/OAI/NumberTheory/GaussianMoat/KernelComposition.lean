import OAI.NumberTheory.GaussianMoat.MultiscaleSchedule

namespace OAI

universe uOmega uAlpha uBeta

namespace GaussianMoat
open scoped BigOperators Classical
namespace FinLaw
noncomputable def pure {Ω : Type uOmega} [Fintype Ω] (ω : Ω) : FinLaw Ω where
  mass ν := if ν=ω then 1 else 0
  nonneg _ := by split_ifs <;> norm_num
  sum_one := by simp

lemma mix_pure {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α] (ω : Ω) (q : Ω → FinLaw α) :
    (pure ω).mix q=q ω := by
  ext a
  simp [mix_mass,pure]

lemma joint_pure_observation {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]
    (ω : Ω) (q : Ω → FinLaw α) (F : Ω × α → β) :
    ((pure ω).joint q).map F=(q ω).map (fun a => F (ω,a)) := by
  rw [joint_observation_fun,mix_pure]
end FinLaw

noncomputable def TimeLaw.at (a : ℕ) : TimeLaw where
  last := a
  law := FinLaw.pure ⟨a,by omega⟩

lemma TimeLaw.at_advance (a : ℕ) (K : ForwardKernel) :
    ((TimeLaw.at a).advance K).law=
      (K.law a).map (fun t => (⟨a+t.val,by omega⟩ : Fin (a+K.bound+1))) := by
  change ((FinLaw.pure (⟨a,by omega⟩ : Fin (a+1))).joint
    (fun t => K.law t.val)).map (addOffsets a K.bound)=_
  rw [FinLaw.joint_pure_observation]
  rfl

lemma SplitSieve.pointEntropy_exact_start (s : SplitSieve) (K : ForwardKernel)
    (z : ℕ → GaussianInt) (a b : ℕ) :
    s.pointEntropy ((TimeLaw.at a).advance K).law (fun t => z t.val) b=
      s.pointEntropy (K.law a) (fun t => z (a+t.val)) b := by
  rw [TimeLaw.at_advance]
  change s.pointEntropy ((K.law a).map
    (fun t => (⟨a+t.val,by omega⟩ : Fin (a+K.bound+1)))) (fun t => z t.val) b = _
  rw [s.pointEntropy_map]
  rfl

theorem TimeLaw.advance_entropy_succ (P : TimeLaw) (K : ForwardKernel) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1≤D)
    (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D) (b : ℕ) :
    s.pointEntropy P.law (fun a => z a.val) b-
      (Real.log 36+2*Real.log (D*(K.bound+1))) ≤
    s.pointEntropy (P.advance K).law (fun a => z a.val) b := by
  let Q := P.law.joint (fun a => K.law a.val)
  have hh := s.pointEntropy_shift Q (fun v => z v.1.val)
    (fun v => z (v.1.val+v.2.val)) b
  have hf := s.pointEntropy_joint_fst P.law (fun a => K.law a.val) (fun a => z a.val) b
  change s.pointEntropy Q (fun v => z v.1.val) b=_ at hf
  rw [hf] at hh
  have he : s.pointEntropy (P.advance K).law (fun a => z a.val) b=
      s.pointEntropy Q (fun v => z (v.1.val+v.2.val)) b := by
    unfold TimeLaw.advance
    rw [s.pointEntropy_map]
    rfl
  have hc : Q.Hf (fun v => z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*(K.bound+1)) := by
    apply displacement_entropy_le
    · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast Nat.le_add_left 1 K.bound)
    · intro v
      have hd := walk_pair_displacement z (by linarith only [hD]) hs
        v.1.val (K.bound+1) v.2.val 0 (by omega) (by omega)
      simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one] using hd
  rw [he]
  linarith only [hh,hc]

theorem commonSchedule_subband_entropy (s : SplitSieve) (hne : s.primes.Nonempty)
    (z : ℕ → GaussianInt) (hinj : Function.Injective z)
    (pre post : List ℕ) (a N : ℕ) {D T U g e : ℝ} {l : ℕ}
    (hD : 1≤D) (hT : 5≤T) (hs : ∀ t, dist (z t:ℂ) (z (t+1):ℂ)≤D)
    (hpT : ∀ p∈s.primes, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hg : 0<g) (hg1 : g≤1/200) (hL : 1≤ s.meanLog) (hU : 0<U)
    (hlog : 2*(1+Real.log 18)≤g*bandScale g U l)
    (hlarge : 640*s.meanLog≤g^5*bandScale g U l)
    (hsize : Real.log 16+Real.log (max D ((latticeBall (4*D)).card:ℝ))≤g^2*bandScale g U l)
    (hdisp : 4*Real.log D+2*Real.log 36≤4*g*bandScale g U l)
    (hgeom : 2*Real.log 16+4*Real.log D≤bandScale g U l/4)
    (hcap : ⌊U/s.meanLog⌋₊≤ s.primes.card)
    (hcost : Real.log 36+2*Real.log (D*((post.sum+N:ℕ)+1)) ≤
      e*(bandSize s g U l:ℝ)*s.meanLog) :
    (1-(1/2:ℝ)^l-80*g-e)*(bandSize s g U l:ℝ)*s.meanLog ≤
      s.pointEntropy ((commonSchedule z
        (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post) N).law a)
          (fun t => z (a+t.val)) (bandSize s g U l) := by
  rw [← s.pointEntropy_exact_start]
  rw [List.append_assoc,TimeLaw.advance_common_append,TimeLaw.advance_common_append,
    TimeLaw.foldl_ofFn]
  let P := pre.foldl (fun Q k => Q.step z k) (TimeLaw.at a)
  have h1 := P.geometric_band_entropy s hne z hinj hD hT hs hpT hg hg1 hL hU
    hlog hlarge hsize hdisp hgeom hcap
  have h2 := (P.run z (bandLength g U) l).advance_entropy_succ
    (commonSchedule z post N) s z hD hs (bandSize s g U l)
  rw [commonSchedule_bound] at h2
  change _ ≤ s.pointEntropy ((P.run z (bandLength g U) l).advance (commonSchedule z post N)).law
    (fun a => z a.val) (bandSize s g U l)
  simp only [Nat.cast_add] at hcost h2
  nlinarith only [h1,h2,hcost]

lemma ForwardKernel.ext_observe (K R : ForwardKernel) (hb : K.bound=R.bound)
    (h : ∀ (a : ℕ) {α : Type} [Fintype α] (f : ℕ → α),
      (K.law a).map (fun t => f (a+t.val))=(R.law a).map (fun t => f (a+t.val))) : K=R := by
  cases K with | mk n p =>
  cases R with | mk m q =>
  dsimp only at hb
  subst m
  congr 1
  funext a
  let f : ℕ → Fin (n+1) := fun t => ⟨min (t-a) n,by omega⟩
  have hh := h a f
  have he : (fun t : Fin (n+1) => f (a+t.val))=id := by
    funext t
    apply Fin.ext
    dsimp only [f,id_eq]
    omega
  simpa only [he,FinLaw.map_id] using hh

lemma ForwardKernel.then_assoc (K R S : ForwardKernel) :
    (K.then R).then S=K.then (R.then S) := by
  apply ForwardKernel.ext_observe
  · exact Nat.add_assoc _ _ _
  · intro a α _ f
    rw [ForwardKernel.then_observe,ForwardKernel.then_observe]
    have hl : ((K.then R).law a).mix
        (fun t => (S.law (a+t.val)).map (fun u => f (a+t.val+u.val))) =
        (K.law a).mix (fun t => (R.law (a+t.val)).mix
          (fun u => (S.law (a+t.val+u.val)).map (fun v => f (a+t.val+u.val+v.val)))) := by
      unfold ForwardKernel.then
      rw [FinLaw.mix_map_left]
      ext x
      simp only [FinLaw.mix_mass,FinLaw.joint_mass,Fintype.sum_prod_type,Finset.mul_sum,
        addOffsets,Nat.add_assoc,mul_assoc]
    rw [hl]
    congr 1
    funext t
    exact (R.then_observe S (a+t.val) f).symm

lemma FinLaw.map_pure {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]
    (ω : Ω) (f : Ω → α) : (FinLaw.pure ω).map f=FinLaw.pure (f ω) := by
  ext a
  simp only [FinLaw.map_mass,FinLaw.pure]
  rw [Finset.sum_eq_single ω]
  · simp only [ite_true,eq_comm]
  · intro ν _ hν
    simp [hν]
  · simp

lemma FinLaw.mix_pure_right {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]
    (p : FinLaw Ω) (f : Ω → α) : p.mix (fun ω => FinLaw.pure (f ω))=p.map f := by
  ext a
  simp only [FinLaw.mix_mass,FinLaw.pure,FinLaw.map_mass,mul_ite,mul_one,mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [eq_comm]

lemma smoothingKernel_zero_law (a : ℕ) :
    (smoothingKernel 0).law a=FinLaw.pure (0 : Fin 1) := by
  change FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1)
  ext x
  have hx : x=0 := Subsingleton.elim _ _
  simp [FinLaw.uniform,FinLaw.pure,hx]

lemma ForwardKernel.then_zero (K : ForwardKernel) : K.then (smoothingKernel 0)=K := by
  apply ForwardKernel.ext_observe
  · exact Nat.add_zero _
  · intro a α _ f
    rw [ForwardKernel.then_observe]
    change (K.law a).mix (fun t => (FinLaw.uniform (Fin 1)).map
      (fun u => f (a+t.val+u.val)))=_
    have hu : FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1) := smoothingKernel_zero_law 0
    simp only [hu,FinLaw.map_pure,Fin.val_zero,Nat.add_zero]
    exact FinLaw.mix_pure_right _ _

lemma ForwardKernel.zero_then (K : ForwardKernel) : (smoothingKernel 0).then K=K := by
  apply ForwardKernel.ext_observe
  · exact Nat.zero_add _
  · intro a α _ f
    rw [ForwardKernel.then_observe]
    change (FinLaw.uniform (Fin 1)).mix
      (fun t => (K.law (a+t.val)).map (fun u => f (a+t.val+u.val)))=_
    have hu : FinLaw.uniform (Fin 1)=FinLaw.pure (0 : Fin 1) := smoothingKernel_zero_law 0
    rw [hu,FinLaw.mix_pure]
    rfl

lemma commonSchedule_append (z : ℕ → GaussianInt) (ns ms : List ℕ) (N : ℕ) :
    commonSchedule z (ns++ms) N=(commonSchedule z ns 0).then (commonSchedule z ms N) := by
  induction ns with
  | nil => exact (ForwardKernel.zero_then _).symm
  | cons n ns ih =>
    rw [List.cons_append,commonSchedule_cons,commonSchedule_cons,ih,ForwardKernel.then_assoc]

end GaussianMoat

end OAI
