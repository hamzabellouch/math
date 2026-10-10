import Mathlib
import OAI.Combinatorics.UniformKServer.UniformWrapper
import OAI.Combinatorics.UniformKServer.StackCoins

namespace OAI

noncomputable section

namespace UniformKServer.BitSampling
open scoped Classical
 theorem mean_injective {A D V : Type*} [Fintype A] [Fintype D] [DecidableEq A] [DecidableEq D] [Fintype V] [Nonempty V]
    (f : A→D) (hf : Function.Injective f) (F : (A→V)→ℝ) :
    mean (fun g : D→V=>F (fun a=>g (f a)))=mean F := by
  let p:=fun d=>d∈Set.range f
  let e:=Equiv.piEquivPiSubtypeProd p (fun _=>V)
  let h : (∀d : {x//p x},V)→ℝ := fun g=>F (fun a=>g ⟨f a,⟨a,rfl⟩⟩)
  have he:=mean_equiv e (fun z=>h z.1)
  change mean (fun g : D→V=>F (fun a=>g (f a)))= _ at he
  rw [he,mean_prod]
  simp only [mean_const]
  let e':A≃Set.range f:=Equiv.ofInjective f hf
  have hh:=mean_equiv (Equiv.arrowCongr e'.symm (Equiv.refl V)) F
  exact hh
end UniformKServer.BitSampling

namespace UniformKServer.UniformWrapper
open scoped Classical

 def coinIndex {H b N : ℕ} (hn : 2*(H*b)≤N) (i : Fin H×Fin b) : Fin N :=
  ⟨2*(finProdFinEquiv i).val,by have hh:=(finProdFinEquiv i).isLt;omega⟩
 theorem coinIndex_injective {H b N : ℕ} (hn : 2*(H*b)≤N) : Function.Injective (coinIndex hn) := by
  intro i j h
  have hh:=congrArg Fin.val h
  apply finProdFinEquiv.injective
  apply Fin.ext
  dsimp [coinIndex] at hh
  omega
 def tapeCoins {H b N : ℕ} (hn : 2*(H*b)≤N) (bs : Fin N→Bool) : Fin H→Fin b→Bool :=
  fun i j=>bs (coinIndex hn (i,j))
 theorem tapeCoins_word {H b N : ℕ} (hn : 2*(H*b)≤N) (bs : Fin N→Bool) :
    BinaryTape.word (tapeCoins hn bs)=(StackCompiler.alternate (List.ofFn bs)).take (H*b) := by
  rw [BinaryTape.word_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take,StackCompiler.alternate_length]
    omega
  · intro i h₁ h₂
    simp only [List.length_ofFn] at h₁
    simp only [List.getElem_ofFn,List.getElem_take]
    rw [StackCompiler.alternate_get _ i (by simp only [List.length_ofFn];omega),List.getElem_ofFn]
    unfold tapeCoins coinIndex
    congr 1
    apply Fin.ext
    simp only [Prod.mk.eta,Equiv.apply_symm_apply]
 theorem tapeCoins_mean {H b N : ℕ} (hn : 2*(H*b)≤N) (f : (Fin H→Fin b→Bool)→ℝ) :
    BitSampling.mean (fun bs : Fin N→Bool=>f (tapeCoins hn bs))=BitSampling.mean f := by
  have hh:=BitSampling.mean_injective (coinIndex hn) (coinIndex_injective hn)
    (fun g : Fin H×Fin b→Bool=>f (fun i j=>g (i,j)))
  have he : BitSampling.mean (fun bs : Fin N→Bool=>f (tapeCoins hn bs))=
      BitSampling.mean (fun g : Fin H×Fin b→Bool=>f (fun i j=>g (i,j))) := by
    exact hh
  rw [he]
  exact BitSampling.mean_equiv (Equiv.curry (Fin H) (Fin b) Bool) f

end UniformKServer.UniformWrapper

end

end OAI
