import OAI.NumberTheory.GaussianMoat.TimeLaw

namespace OAI

universe uOmega uAlpha uBeta uGamma uDelta uEpsilon uZeta uIota

namespace GaussianMoat

section
open scoped BigOperators Classical

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma mix_map_left (p : FinLaw Ω) (f : Ω → α) (q : α → FinLaw β) :
    (p.map f).mix q = p.mix (fun ω => q (f ω)) := by
  ext b
  simp only [mix_mass,map_mass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp

lemma mix_assoc (p : FinLaw Ω) (q : Ω → FinLaw α) (r : α → FinLaw β) :
    (p.mix q).mix r = p.mix (fun ω => (q ω).mix r) := by
  ext b
  simp only [mix_mass,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma joint_observation (p : FinLaw Ω) (q : Ω → FinLaw α) (F : Ω → α → β) :
    (p.joint q).map (fun v => F v.1 v.2) = p.mix (fun ω => (q ω).map (F ω)) := by
  have h := congrArg (fun r : FinLaw (Ω × β) => r.map Prod.snd) (joint_map_fiber p q F)
  simpa only [map_comp,joint_map_snd,Function.comp_def] using h

lemma joint_associate (p : FinLaw Ω) (q : Ω → FinLaw α) (r : Ω → α → FinLaw β) :
    ((p.joint q).joint (fun v => r v.1 v.2)).map (fun v => (v.1.1,(v.1.2,v.2))) =
      p.joint (fun ω => (q ω).joint (r ω)) := by
  ext v
  rcases v with ⟨ω,a,b⟩
  change ((p.joint q).joint (fun v => r v.1 v.2)).map (Equiv.prodAssoc Ω α β) (ω,a,b) = _
  rw [map_equiv_mass]
  simp only [Equiv.prodAssoc_symm_apply,joint_mass,mul_assoc]

end FinLaw

structure ForwardKernel where
  bound : ℕ
  law : ℕ → FinLaw (Fin (bound+1))

noncomputable def addOffsets (n m : ℕ) : Fin (n+1) × Fin (m+1) → Fin (n+m+1) :=
  fun v => ⟨v.1.val+v.2.val,by omega⟩

noncomputable def ForwardKernel.then (K R : ForwardKernel) : ForwardKernel where
  bound := K.bound+R.bound
  law := fun a => ((K.law a).joint (fun i => R.law (a+i.val))).map
    (addOffsets K.bound R.bound)

noncomputable def differenceKernel (z : ℕ → GaussianInt) (n : ℕ) : ForwardKernel where
  bound := n
  law := fun a => ((FinLaw.uniform Bool).joint (fun _ =>
    differenceLaw (fun t => z (a+t)) n)).map (fun v => if v.1 then v.2.1 else v.2.2)

noncomputable def smoothingKernel (n : ℕ) : ForwardKernel where
  bound := n
  law := fun _ => FinLaw.uniform (Fin (n+1))

noncomputable def commonSchedule (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) : ForwardKernel :=
  ns.foldr (fun n K => (differenceKernel z n).then K) (smoothingKernel N)

@[simp] lemma commonSchedule_bound (z : ℕ → GaussianInt) (ns : List ℕ) (N : ℕ) :
    (commonSchedule z ns N).bound = ns.sum+N := by
  induction ns with
  | nil => simp [commonSchedule,smoothingKernel]
  | cons n ns ih =>
    change n+(commonSchedule z ns N).bound = _
    rw [ih,List.sum_cons,Nat.add_assoc]

@[simp] lemma commonSchedule_cons (z : ℕ → GaussianInt) (n : ℕ) (ns : List ℕ) (N : ℕ) :
    commonSchedule z (n::ns) N = (differenceKernel z n).then (commonSchedule z ns N) := rfl

noncomputable def TimeLaw.advance (P : TimeLaw) (K : ForwardKernel) : TimeLaw where
  last := P.last+K.bound
  law := (P.law.joint (fun a => K.law a.val)).map (addOffsets P.last K.bound)

lemma ForwardKernel.displacement_entropy (K : ForwardKernel) (a : ℕ)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) :
    (K.law a).Hf (fun i => z (a+i.val)-z a) ≤
      Real.log 36+2*Real.log (D*K.bound) := by
  apply displacement_entropy_le
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro i
    simpa only [Nat.add_zero] using walk_pair_displacement z (by linarith only [hD]) hstep
      a K.bound i.val 0 (by omega) (by omega)

lemma TimeLaw.advance_displacement_entropy (P : TimeLaw) (K : ForwardKernel)
    (z : ℕ → GaussianInt) {D : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) (hK : 1 ≤ K.bound) :
    (P.law.joint (fun a => K.law a.val)).Hf
      (fun v => z (v.1.val+v.2.val)-z v.1.val) ≤
      Real.log 36+2*Real.log (D*K.bound) := by
  apply displacement_entropy_le
  · exact one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hK)
  · intro v
    simpa only [Nat.add_zero] using walk_pair_displacement z (by linarith only [hD]) hstep
      v.1.val K.bound v.2.val 0 (by omega) (by omega)

lemma entropy_step_deficit {b q : ℕ} {L F E E' g e C : ℝ}
    (hq : 0 < q) (hL : 0 ≤ L) (hg : 0 ≤ g) (hg1 : g ≤ 1/100)
    (hbq : (b:ℝ) ≤ g*q) (hF : (1-30*g)*L ≤ F)
    (hE : (1-e)*(q:ℝ)*L ≤ E) (hC : C ≤ 8*g*q*L)
    (hstep : (b:ℝ)*((q-b:ℕ)*F+E-C) ≤ 2*(q:ℝ)*E') :
    (1-e/2-20*g)*(b:ℝ)*L ≤ E' := by
  have hqr : (0:ℝ) < q := by exact_mod_cast hq
  have hbqr : (b:ℝ) ≤ q := by nlinarith only [hbq,hg1,hqr]
  have hbqnat : b ≤ q := by exact_mod_cast hbqr
  rw [Nat.cast_sub hbqnat] at hstep
  have hqbn : 0 ≤ (q:ℝ)-b := by linarith only [hbqr]
  have hFb := mul_le_mul_of_nonneg_left hF hqbn
  have hgl : 0 ≤ (1-30*g)*L := mul_nonneg (by linarith only [hg1]) hL
  have hbL := mul_le_mul_of_nonneg_right hbq hgl
  have hgg := mul_nonneg (mul_nonneg hg hg) (mul_nonneg hqr.le hL)
  have hgql : 0 ≤ g*(q:ℝ)*L := by positivity
  have hcore : (2-e-40*g)*(q:ℝ)*L ≤ ((q:ℝ)-b)*F+E-C := by
    nlinarith only [hFb,hbL,hE,hC,hgg,hgql]
  have hm := mul_le_mul_of_nonneg_left hcore (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0:ℝ)<2) hqr)).mp
  calc
    _ = (b:ℝ)*((2-e-40*g)*(q:ℝ)*L) := by ring
    _ ≤ (b:ℝ)*(((q:ℝ)-b)*F+E-C) := hm
    _ ≤ _ := hstep

theorem TimeLaw.step_deficit (P : TimeLaw) (s : SplitSieve)
    (z : ℕ → GaussianInt) {D g e : ℝ} (hD : 1 ≤ D)
    (hstep : ∀ t, dist (z t:ℂ) (z (t+1):ℂ) ≤ D) {n b q : ℕ}
    (hn : 1 ≤ n) (hb : 0 < b) (hbq : b < q) (hq : q ≤ s.primes.card)
    (hg : 0 ≤ g) (hg1 : g ≤ 1/100) (hL : 0 ≤ s.meanLog)
    (hratio : (b:ℝ) ≤ g*q)
    (hfresh : ∀ a : Fin (P.last+1), (1-30*g)*s.meanLog ≤ s.freshCoordinate
      (differenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) b (by omega))
    (hE : (1-e)*(q:ℝ)*s.meanLog ≤ s.pointEntropy P.law (fun a => z a.val) q)
    (hcost : 2*(Real.log 36+2*Real.log (D*n)) ≤ 8*g*q*s.meanLog) :
    (1-e/2-20*g)*(b:ℝ)*s.meanLog ≤
      s.pointEntropy (P.step z n).law (fun a => z a.val) b := by
  exact entropy_step_deficit (by omega) hL hg hg1 hratio le_rfl hE hcost
    (P.step_enrichment s z hD hstep hn hb hbq hq hfresh)

lemma deficit_iteration (l : ℕ) {g : ℝ} (hg : 0 ≤ g) (e : ℕ → ℝ)
    (h0 : e 0 ≤ 1) (hnext : ∀ j < l, e (j+1) ≤ e j/2+20*g) :
    e l ≤ (1/2:ℝ)^l+40*g := by
  induction l with
  | zero => simpa only [pow_zero] using h0.trans (le_add_of_nonneg_right (by positivity))
  | succ l ih =>
    have hi := ih (fun j hj => hnext j (by omega))
    have hn := hnext l (by omega)
    rw [pow_succ]
    linarith only [hi,hn]

end

section
namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

lemma joint_observation_fun (p : FinLaw Ω) (q : Ω → FinLaw α) (F : Ω × α → β) :
    (p.joint q).map F = p.mix (fun ω => (q ω).map (fun a => F (ω,a))) := by
  exact joint_observation p q (fun ω a => F (ω,a))

lemma mix_comm (p : FinLaw Ω) (q : FinLaw α) (r : Ω → α → FinLaw β) :
    p.mix (fun ω => q.mix (r ω)) = q.mix (fun a => p.mix (fun ω => r ω a)) := by
  ext b
  simp only [mix_mass,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro ω _
  ring

end FinLaw
open scoped BigOperators Classical

lemma TimeLaw.advance_difference (P : TimeLaw) (z : ℕ → GaussianInt) (n : ℕ) :
    P.advance (differenceKernel z n) = P.step z n := by
  unfold TimeLaw.advance TimeLaw.step differenceKernel
  congr 1
  dsimp only
  rw [FinLaw.joint_observation_fun]
  conv_lhs => arg 2; ext a; rw [FinLaw.map_comp,FinLaw.joint_observation_fun]
  rw [FinLaw.mix_comm,FinLaw.joint_observation_fun]
  conv_rhs => arg 2; ext c; rw [FinLaw.joint_observation_fun]
  apply congrArg
  funext c
  apply congrArg
  funext a
  apply congrArg
  funext ij
  apply Fin.ext
  dsimp only [Function.comp_def,addOffsets,endpointTime]
  split_ifs <;> rfl

end

namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} {ε : Type uEpsilon} [Fintype Ω]

noncomputable def cIf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) : ℝ :=
  p.cHf X O-p.cHf X (fun ω => (O ω,Y ω))

lemma cIf_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    0 ≤ p.cIf X Y O := sub_nonneg.mpr (p.cHf_mono X O Y)

lemma cIf_comm (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O = p.cIf Y X O := by
  unfold cIf cHf
  have he : p.Hf (fun ω => (X ω,(O ω,Y ω))) =
      p.Hf (fun ω => (Y ω,(O ω,X ω))) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  rw [he,p.Hf_pair_comm O Y,p.Hf_pair_comm O X]
  ring

lemma cIf_le_cHf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O ≤ p.cHf X O := by
  have h := p.cHf_nonneg X (fun ω => (O ω,Y ω))
  unfold cIf
  linarith

lemma cIf_le_Hf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (O : Ω → γ) :
    p.cIf X Y O ≤ p.Hf Y := by
  rw [p.cIf_comm]
  exact (p.cIf_le_cHf Y X O).trans (p.cHf_le_Hf Y O)

lemma cIf_chain (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → δ) (O : Ω → γ) :
    p.cIf X (fun ω => (Y ω,Z ω)) O =
      p.cIf X Y O+p.cIf X Z (fun ω => (O ω,Y ω)) := by
  unfold cIf
  have he : p.cHf X (fun ω => (O ω,(Y ω,Z ω))) =
      p.cHf X (fun ω => ((O ω,Y ω),Z ω)) := by
    unfold cHf
    rw [p.Hf_pair_assoc O Y Z]
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq,and_assoc]
  rw [he]
  ring

lemma cIf_conditioning_cost (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (O : Ω → γ) (S : Ω → δ) :
    p.cIf X Y (fun ω => (O ω,S ω)) ≤ p.cIf X Y O+p.Hf S := by
  have h1 := p.cHf_mono X O S
  have h2 := p.cHf_mono S O Y
  have h3 := p.cHf_le_Hf S O
  have h4 := p.cHf_nonneg S (fun ω => (X ω,(O ω,Y ω)))
  have h5 := p.cHf_chain X S (fun ω => (O ω,Y ω))
  have h6 := p.cHf_chain S X (fun ω => (O ω,Y ω))
  have he : p.cHf (fun ω => (X ω,S ω)) (fun ω => (O ω,Y ω)) =
      p.cHf (fun ω => (S ω,X ω)) (fun ω => (O ω,Y ω)) := by
    unfold cHf
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    tauto
  have he' : p.cHf X (fun ω => ((O ω,S ω),Y ω)) =
      p.cHf X (fun ω => (S ω,(O ω,Y ω))) := by
    unfold cHf
    congr 1 <;> apply p.Hf_eq_of_fibers <;> intro ω ν <;>
      simp only [Prod.mk.injEq] <;> tauto
  unfold cIf
  rw [he']
  linarith only [h1,h2,h3,h4,h5,h6,he]

theorem cIf_transport (p : FinLaw Ω) (X : Ω → α) (O : Ω → β)
    (X' : Ω → γ) (O' : Ω → δ) (W : Ω → ε) {ζ : Type uZeta} (S : Ω → ζ)
    (hO : ∀ ω ν, (O ω,S ω)=(O ν,S ν) ↔ (O' ω,S ω)=(O' ν,S ν))
    (hX : ∀ ω ν, (X ω,O ω,S ω)=(X ν,O ν,S ν) ↔
      (X' ω,O' ω,S ω)=(X' ν,O' ν,S ν)) :
    p.cIf X (fun ω => (S ω,W ω)) O ≤ p.cIf X' W O'+2*p.Hf S := by
  have he : p.cIf X W (fun ω => (O ω,S ω)) =
      p.cIf X' W (fun ω => (O' ω,S ω)) := by
    rw [p.cIf_comm X W,p.cIf_comm X' W]
    unfold cIf cHf
    congr 2
    · apply p.Hf_eq_of_fibers
      intro ω ν
      simp only [Prod.mk.injEq,hO]
    · exact p.Hf_eq_of_fibers _ _ hO
    · apply p.Hf_eq_of_fibers
      intro ω ν
      have hh := hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
    · apply p.Hf_eq_of_fibers
      intro ω ν
      have hh := hX ω ν
      simp only [Prod.mk.injEq] at hh ⊢
      tauto
  rw [p.cIf_chain X S W O,he]
  have h1 := p.cIf_le_Hf X S O
  have h2 := p.cIf_conditioning_cost X' W O' S
  linarith

lemma cHf_eq_conditionOn [Fintype β] (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.cHf X Y = ∑ a, p.map Y a*(p.conditionOn Y a).Hf X := by
  let C := outputCode X
  have hh := p.condH_eq_conditionOn C Y
  have hx (r : FinLaw Ω) : r.Hf C = r.Hf X := by
    apply r.Hf_eq_of_fibers
    intro ω ν
    exact outputCode_eq_iff X ω ν
  have hpair : p.Hf (fun ω => (C ω,Y ω)) = p.Hf (fun ω => (X ω,Y ω)) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq,C,outputCode_eq_iff]
  simpa only [condH,← Hf_eq_H,hx,hpair,cHf] using hh

end FinLaw

open scoped BigOperators Classical

theorem SplitSieve.pointEntropy_shift {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (X Y : Ω → GaussianInt) (b : ℕ) :
    s.pointEntropy p X b ≤ s.pointEntropy p Y b+p.Hf (fun ω => Y ω-X ω) := by
  have h (σ : Fin s.primes.card → Bool) (π : Equiv.Perm (Fin s.primes.card)) :
      p.Hf (FinLaw.prefixVar (fun ω => s.residueVector σ (X ω)) π b) ≤
        p.Hf (FinLaw.prefixVar (fun ω => s.residueVector σ (Y ω)) π b)+
          p.Hf (fun ω => Y ω-X ω) := by
    apply (p.Hf_le_of_determined _ (fun ω =>
      (FinLaw.prefixVar (fun ν => s.residueVector σ (Y ν)) π b ω,Y ω-X ω)) ?_).trans
      (p.Hf_pair_subadd _ _)
    intro ω ν hh
    funext i
    by_cases hi : i.val<b
    · have hy : s.residueVector σ (Y ω) (π i)=s.residueVector σ (Y ν) (π i) := by
        simpa [FinLaw.prefixVar,hi] using congrFun (congrArg Prod.fst hh) i
      have hd := congrArg (residueCode (signedFactor (s.factor (s.enumeration (π i))) (σ (π i)))) (congrArg Prod.snd hh)
      have hx := residueCode_sub hy hd
      simpa only [sub_sub_cancel,SplitSieve.residueVector,FinLaw.prefixVar,hi,ite_eq_left]
        using congrArg some hx
    · simp [FinLaw.prefixVar,hi]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => h σ π))
  simpa only [SplitSieve.pointEntropy,FinLaw.signedEntropy,FinLaw.orderedEntropy,
    Finset.expect_add_distrib,Fintype.expect_const] using hh

lemma residue_observation_shift {Ω : Type uOmega} {ι : Type uIota} (f : ι → GaussianInt)
    (X Y : Ω → GaussianInt) (ω ν : Ω) :
    ((fun i => residueCode (f i) (X ω)),Y ω-X ω)=
      ((fun i => residueCode (f i) (X ν)),Y ν-X ν) ↔
    ((fun i => residueCode (f i) (Y ω)),Y ω-X ω)=
      ((fun i => residueCode (f i) (Y ν)),Y ν-X ν) := by
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hx,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h := residueCode_add (congrFun hx i) (congrArg (residueCode (f i)) hd)
    simpa only [add_sub_cancel] using h
  · rintro ⟨hy,hd⟩
    refine ⟨?_,hd⟩
    funext i
    have h := residueCode_sub (congrFun hy i) (congrArg (residueCode (f i)) hd)
    simpa only [sub_sub_cancel] using h

end GaussianMoat

end OAI
